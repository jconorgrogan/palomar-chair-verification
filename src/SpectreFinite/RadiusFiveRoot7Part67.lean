module

public import SpectreFinite.RadiusFiveRoot7Part66
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable1
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node171Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(5,2),(8,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3)]
  | 29 => [(4,2),(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3),(3,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(1,5),(3,5)]
  | 48 => [(0,3),(6,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,4),(6,2)]
  | 52 => [(5,4),(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(2,0),(2,4)]
  | 59 => [(1,3),(7,3)]
  | 60 => [(5,2)]
  | 61 => [(4,3),(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(3,1),(7,1)]
  | 68 => [(0,1),(6,5)]
  | 69 => [(0,4),(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(1,0),(7,0)]
  | 78 => [(0,3),(0,4),(6,1),(6,2)]
  | 79 => [(5,1),(5,4),(8,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(5,3),(7,1),(8,3)]
  | 86 => [(7,5),(8,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node171Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2),(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(3,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(2,0),(2,4)]
  | 59 => some [(1,3),(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(3,1),(7,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0),(7,0)]
  | 78 => some [(0,3),(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(5,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node171Domains2_fast_eq : root7Node171Domains2 = expandDomains root7Node171Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node171Domains2 v = expandDomains root7Node171Domains2Fast v from by decide) v
theorem root7Node171Step2Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq (by decide)
theorem root7Node171Step2Narrowing_checked :
    checkNarrowing table57 root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root7Node171Domains1 root7Node171Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node171Step2Chunk0_0_checked, root7Node171Step2Chunk0_1_checked, root7Node171Step2Chunk0_2_checked, root7Node171Step2Chunk0_3_checked, root7Node171Step2Chunk0_4_checked, root7Node171Step2Chunk0_5_checked, root7Node171Step2Chunk1_0_checked, root7Node171Step2Chunk1_1_checked, root7Node171Step2Chunk1_2_checked, root7Node171Step2Chunk1_3_checked, root7Node171Step2Chunk1_4_checked, root7Node171Step2Chunk1_5_checked, root7Node171Step2Chunk2_0_checked, root7Node171Step2Chunk2_1_checked, root7Node171Step2Chunk2_2_checked, root7Node171Step2Chunk2_3_checked, root7Node171Step2Chunk2_4_checked, root7Node171Step2Chunk2_5_checked, root7Node171Step2Chunk3_0_checked, root7Node171Step2Chunk3_1_checked, root7Node171Step2Chunk3_2_checked, root7Node171Step2Chunk3_3_checked, root7Node171Step2Chunk3_4_checked, root7Node171Step2Chunk3_5_checked, root7Node171Step2Chunk4_0_checked, root7Node171Step2Chunk4_1_checked, root7Node171Step2Chunk4_2_checked, root7Node171Step2Chunk4_3_checked, root7Node171Step2Chunk4_4_checked, root7Node171Step2Chunk4_5_checked, root7Node171Step2Chunk5_0_checked, root7Node171Step2Chunk5_1_checked, root7Node171Step2Chunk5_2_checked, root7Node171Step2Chunk5_3_checked, root7Node171Step2Chunk5_4_checked, root7Node171Step2Chunk5_5_checked, root7Node171Step2Chunk6_0_checked, root7Node171Step2Chunk6_1_checked, root7Node171Step2Chunk6_2_checked, root7Node171Step2Chunk6_3_checked, root7Node171Step2Chunk6_4_checked, root7Node171Step2Chunk6_5_checked, root7Node171Step2Chunk7_0_checked, root7Node171Step2Chunk7_1_checked, root7Node171Step2Chunk7_2_checked, root7Node171Step2Chunk7_3_checked, root7Node171Step2Chunk7_4_checked, root7Node171Step2Chunk7_5_checked, root7Node171Step2Chunk8_0_checked, root7Node171Step2Chunk8_1_checked, root7Node171Step2Chunk8_2_checked, root7Node171Step2Chunk8_3_checked, root7Node171Step2Chunk8_4_checked, root7Node171Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node171Step2_checked :
    checkReplacement table57 root7Node171Domains1 root7Node171Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node171Domains1 root7Node171Domains2
    root7Node171Domains1Fast root7Node171Domains2Fast
    root7Node171Domains1_fast_eq root7Node171Domains2_fast_eq
    root7Node171Step2Narrowing_checked (by decide)
def root7Node171Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(5,2),(8,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3)]
  | 29 => [(4,2),(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3),(3,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(1,5),(3,5)]
  | 48 => [(0,3),(6,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,4),(6,2)]
  | 52 => [(5,4),(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(2,0),(2,4)]
  | 59 => [(1,3),(7,3)]
  | 60 => [(5,2)]
  | 61 => [(4,3),(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(3,1),(7,1)]
  | 68 => [(0,1),(6,5)]
  | 69 => [(0,4),(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(1,0),(7,0)]
  | 78 => [(0,4),(6,2)]
  | 79 => [(5,4),(8,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node171Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2),(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(3,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(2,0),(2,4)]
  | 59 => some [(1,3),(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(3,1),(7,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0),(7,0)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node171Domains3_fast_eq : root7Node171Domains3 = expandDomains root7Node171Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node171Domains3 v = expandDomains root7Node171Domains3Fast v from by decide) v
theorem root7Node171Step3Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq (by decide)
theorem root7Node171Step3Narrowing_checked :
    checkNarrowing table52 root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root7Node171Domains2 root7Node171Domains3 (by
      simp only [List.all_cons, List.all_nil, root7Node171Step3Chunk0_0_checked, root7Node171Step3Chunk0_1_checked, root7Node171Step3Chunk0_2_checked, root7Node171Step3Chunk0_3_checked, root7Node171Step3Chunk0_4_checked, root7Node171Step3Chunk0_5_checked, root7Node171Step3Chunk1_0_checked, root7Node171Step3Chunk1_1_checked, root7Node171Step3Chunk1_2_checked, root7Node171Step3Chunk1_3_checked, root7Node171Step3Chunk1_4_checked, root7Node171Step3Chunk1_5_checked, root7Node171Step3Chunk2_0_checked, root7Node171Step3Chunk2_1_checked, root7Node171Step3Chunk2_2_checked, root7Node171Step3Chunk2_3_checked, root7Node171Step3Chunk2_4_checked, root7Node171Step3Chunk2_5_checked, root7Node171Step3Chunk3_0_checked, root7Node171Step3Chunk3_1_checked, root7Node171Step3Chunk3_2_checked, root7Node171Step3Chunk3_3_checked, root7Node171Step3Chunk3_4_checked, root7Node171Step3Chunk3_5_checked, root7Node171Step3Chunk4_0_checked, root7Node171Step3Chunk4_1_checked, root7Node171Step3Chunk4_2_checked, root7Node171Step3Chunk4_3_checked, root7Node171Step3Chunk4_4_checked, root7Node171Step3Chunk4_5_checked, root7Node171Step3Chunk5_0_checked, root7Node171Step3Chunk5_1_checked, root7Node171Step3Chunk5_2_checked, root7Node171Step3Chunk5_3_checked, root7Node171Step3Chunk5_4_checked, root7Node171Step3Chunk5_5_checked, root7Node171Step3Chunk6_0_checked, root7Node171Step3Chunk6_1_checked, root7Node171Step3Chunk6_2_checked, root7Node171Step3Chunk6_3_checked, root7Node171Step3Chunk6_4_checked, root7Node171Step3Chunk6_5_checked, root7Node171Step3Chunk7_0_checked, root7Node171Step3Chunk7_1_checked, root7Node171Step3Chunk7_2_checked, root7Node171Step3Chunk7_3_checked, root7Node171Step3Chunk7_4_checked, root7Node171Step3Chunk7_5_checked, root7Node171Step3Chunk8_0_checked, root7Node171Step3Chunk8_1_checked, root7Node171Step3Chunk8_2_checked, root7Node171Step3Chunk8_3_checked, root7Node171Step3Chunk8_4_checked, root7Node171Step3Chunk8_5_checked, Bool.true_and])
theorem root7Node171Step3_checked :
    checkReplacement table52 root7Node171Domains2 root7Node171Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root7Node171Domains2 root7Node171Domains3
    root7Node171Domains2Fast root7Node171Domains3Fast
    root7Node171Domains2_fast_eq root7Node171Domains3_fast_eq
    root7Node171Step3Narrowing_checked (by decide)
def root7Node171Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3)]
  | 29 => [(4,2),(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3),(3,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(1,5),(3,5)]
  | 48 => [(0,3),(6,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,4),(6,2)]
  | 52 => [(5,4),(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(2,0),(2,4)]
  | 59 => [(1,3),(7,3)]
  | 60 => [(5,2)]
  | 61 => [(4,3),(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(3,1),(7,1)]
  | 68 => [(0,1),(6,5)]
  | 69 => [(0,4),(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(1,0),(7,0)]
  | 78 => [(0,4),(6,2)]
  | 79 => [(5,4),(8,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node171Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(3,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(2,0),(2,4)]
  | 59 => some [(1,3),(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(3,1),(7,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0),(7,0)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node171Domains4_fast_eq : root7Node171Domains4 = expandDomains root7Node171Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node171Domains4 v = expandDomains root7Node171Domains4Fast v from by decide) v
theorem root7Node171Step4Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq (by decide)
theorem root7Node171Step4Narrowing_checked :
    checkNarrowing table1 root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkNarrowing_flatten table1Scope [table1Rows0_0,table1Rows0_1,table1Rows0_2,table1Rows0_3,table1Rows0_4,table1Rows0_5,table1Rows1_0,table1Rows1_1,table1Rows1_2,table1Rows1_3,table1Rows1_4,table1Rows1_5,table1Rows2_0,table1Rows2_1,table1Rows2_2,table1Rows2_3,table1Rows2_4,table1Rows2_5,table1Rows3_0,table1Rows3_1,table1Rows3_2,table1Rows3_3,table1Rows3_4,table1Rows3_5,table1Rows4_0,table1Rows4_1,table1Rows4_2,table1Rows4_3,table1Rows4_4,table1Rows4_5,table1Rows5_0,table1Rows5_1,table1Rows5_2,table1Rows5_3,table1Rows5_4,table1Rows5_5,table1Rows6_0,table1Rows6_1,table1Rows6_2,table1Rows6_3,table1Rows6_4,table1Rows6_5,table1Rows7_0,table1Rows7_1,table1Rows7_2,table1Rows7_3,table1Rows7_4,table1Rows7_5,table1Rows8_0,table1Rows8_1,table1Rows8_2,table1Rows8_3,table1Rows8_4,table1Rows8_5]
    root7Node171Domains3 root7Node171Domains4 (by
      simp only [List.all_cons, List.all_nil, root7Node171Step4Chunk0_0_checked, root7Node171Step4Chunk0_1_checked, root7Node171Step4Chunk0_2_checked, root7Node171Step4Chunk0_3_checked, root7Node171Step4Chunk0_4_checked, root7Node171Step4Chunk0_5_checked, root7Node171Step4Chunk1_0_checked, root7Node171Step4Chunk1_1_checked, root7Node171Step4Chunk1_2_checked, root7Node171Step4Chunk1_3_checked, root7Node171Step4Chunk1_4_checked, root7Node171Step4Chunk1_5_checked, root7Node171Step4Chunk2_0_checked, root7Node171Step4Chunk2_1_checked, root7Node171Step4Chunk2_2_checked, root7Node171Step4Chunk2_3_checked, root7Node171Step4Chunk2_4_checked, root7Node171Step4Chunk2_5_checked, root7Node171Step4Chunk3_0_checked, root7Node171Step4Chunk3_1_checked, root7Node171Step4Chunk3_2_checked, root7Node171Step4Chunk3_3_checked, root7Node171Step4Chunk3_4_checked, root7Node171Step4Chunk3_5_checked, root7Node171Step4Chunk4_0_checked, root7Node171Step4Chunk4_1_checked, root7Node171Step4Chunk4_2_checked, root7Node171Step4Chunk4_3_checked, root7Node171Step4Chunk4_4_checked, root7Node171Step4Chunk4_5_checked, root7Node171Step4Chunk5_0_checked, root7Node171Step4Chunk5_1_checked, root7Node171Step4Chunk5_2_checked, root7Node171Step4Chunk5_3_checked, root7Node171Step4Chunk5_4_checked, root7Node171Step4Chunk5_5_checked, root7Node171Step4Chunk6_0_checked, root7Node171Step4Chunk6_1_checked, root7Node171Step4Chunk6_2_checked, root7Node171Step4Chunk6_3_checked, root7Node171Step4Chunk6_4_checked, root7Node171Step4Chunk6_5_checked, root7Node171Step4Chunk7_0_checked, root7Node171Step4Chunk7_1_checked, root7Node171Step4Chunk7_2_checked, root7Node171Step4Chunk7_3_checked, root7Node171Step4Chunk7_4_checked, root7Node171Step4Chunk7_5_checked, root7Node171Step4Chunk8_0_checked, root7Node171Step4Chunk8_1_checked, root7Node171Step4Chunk8_2_checked, root7Node171Step4Chunk8_3_checked, root7Node171Step4Chunk8_4_checked, root7Node171Step4Chunk8_5_checked, Bool.true_and])
theorem root7Node171Step4_checked :
    checkReplacement table1 root7Node171Domains3 root7Node171Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root7Node171Domains3 root7Node171Domains4
    root7Node171Domains3Fast root7Node171Domains4Fast
    root7Node171Domains3_fast_eq root7Node171Domains4_fast_eq
    root7Node171Step4Narrowing_checked (by decide)
def root7Node172Domains0 : Domains 91 State := restrict root7Node171Domains4 20 (1,5)
def root7Node172Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(3,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(2,0),(2,4)]
  | 59 => some [(1,3),(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(3,1),(7,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0),(7,0)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node172Domains0_fast_eq : root7Node172Domains0 = expandDomains root7Node172Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node172Domains0 v = expandDomains root7Node172Domains0Fast v from by decide) v
def root7Node172Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3),(3,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,4),(6,2)]
  | 52 => [(5,4),(8,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(2,0)]
  | 59 => [(7,3)]
  | 60 => [(5,2)]
  | 61 => [(4,3),(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(3,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(1,0)]
  | 78 => [(0,4),(6,2)]
  | 79 => [(5,4),(8,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node172Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(3,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(2,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(3,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node172Domains1_fast_eq : root7Node172Domains1 = expandDomains root7Node172Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node172Domains1 v = expandDomains root7Node172Domains1Fast v from by decide) v
theorem root7Node172Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq (by decide)
theorem root7Node172Step1Narrowing_checked :
    checkNarrowing table36 root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root7Node172Domains0 root7Node172Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node172Step1Chunk0_0_checked, root7Node172Step1Chunk0_1_checked, root7Node172Step1Chunk0_2_checked, root7Node172Step1Chunk0_3_checked, root7Node172Step1Chunk0_4_checked, root7Node172Step1Chunk0_5_checked, root7Node172Step1Chunk1_0_checked, root7Node172Step1Chunk1_1_checked, root7Node172Step1Chunk1_2_checked, root7Node172Step1Chunk1_3_checked, root7Node172Step1Chunk1_4_checked, root7Node172Step1Chunk1_5_checked, root7Node172Step1Chunk2_0_checked, root7Node172Step1Chunk2_1_checked, root7Node172Step1Chunk2_2_checked, root7Node172Step1Chunk2_3_checked, root7Node172Step1Chunk2_4_checked, root7Node172Step1Chunk2_5_checked, root7Node172Step1Chunk3_0_checked, root7Node172Step1Chunk3_1_checked, root7Node172Step1Chunk3_2_checked, root7Node172Step1Chunk3_3_checked, root7Node172Step1Chunk3_4_checked, root7Node172Step1Chunk3_5_checked, root7Node172Step1Chunk4_0_checked, root7Node172Step1Chunk4_1_checked, root7Node172Step1Chunk4_2_checked, root7Node172Step1Chunk4_3_checked, root7Node172Step1Chunk4_4_checked, root7Node172Step1Chunk4_5_checked, root7Node172Step1Chunk5_0_checked, root7Node172Step1Chunk5_1_checked, root7Node172Step1Chunk5_2_checked, root7Node172Step1Chunk5_3_checked, root7Node172Step1Chunk5_4_checked, root7Node172Step1Chunk5_5_checked, root7Node172Step1Chunk6_0_checked, root7Node172Step1Chunk6_1_checked, root7Node172Step1Chunk6_2_checked, root7Node172Step1Chunk6_3_checked, root7Node172Step1Chunk6_4_checked, root7Node172Step1Chunk6_5_checked, root7Node172Step1Chunk7_0_checked, root7Node172Step1Chunk7_1_checked, root7Node172Step1Chunk7_2_checked, root7Node172Step1Chunk7_3_checked, root7Node172Step1Chunk7_4_checked, root7Node172Step1Chunk7_5_checked, root7Node172Step1Chunk8_0_checked, root7Node172Step1Chunk8_1_checked, root7Node172Step1Chunk8_2_checked, root7Node172Step1Chunk8_3_checked, root7Node172Step1Chunk8_4_checked, root7Node172Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node172Step1_checked :
    checkReplacement table36 root7Node172Domains0 root7Node172Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node172Domains0 root7Node172Domains1
    root7Node172Domains0Fast root7Node172Domains1Fast
    root7Node172Domains0_fast_eq root7Node172Domains1_fast_eq
    root7Node172Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
