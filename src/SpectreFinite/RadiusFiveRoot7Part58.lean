module

public import SpectreFinite.RadiusFiveRoot7Part57
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable26
public import SpectreFinite.RadiusFiveTable30
public import SpectreFinite.RadiusFiveTable46
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node145Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
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
  | 20 => [(1,5),(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3)]
  | 29 => [(4,2),(7,0)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(5,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(6,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(6,3)]
  | 58 => [(2,0),(2,2),(2,4)]
  | 59 => [(1,3),(3,3),(7,3)]
  | 60 => [(5,2)]
  | 61 => [(1,1),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5)]
  | 66 => [(0,2),(6,0)]
  | 67 => [(1,1),(3,1),(7,1)]
  | 68 => [(0,1),(6,5)]
  | 69 => [(0,4),(6,2)]
  | 70 => [(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(5,2),(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(1,0),(7,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node145Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
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
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4)]
  | 59 => some [(1,3),(3,3),(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5)]
  | 66 => some [(0,2),(6,0)]
  | 67 => some [(1,1),(3,1),(7,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2),(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0),(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node145Domains2_fast_eq : root7Node145Domains2 = expandDomains root7Node145Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node145Domains2 v = expandDomains root7Node145Domains2Fast v from by decide) v
theorem root7Node145Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq (by decide)
theorem root7Node145Step2Narrowing_checked :
    checkNarrowing table56 root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node145Domains1 root7Node145Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node145Step2Chunk0_0_checked, root7Node145Step2Chunk0_1_checked, root7Node145Step2Chunk0_2_checked, root7Node145Step2Chunk0_3_checked, root7Node145Step2Chunk0_4_checked, root7Node145Step2Chunk0_5_checked, root7Node145Step2Chunk1_0_checked, root7Node145Step2Chunk1_1_checked, root7Node145Step2Chunk1_2_checked, root7Node145Step2Chunk1_3_checked, root7Node145Step2Chunk1_4_checked, root7Node145Step2Chunk1_5_checked, root7Node145Step2Chunk2_0_checked, root7Node145Step2Chunk2_1_checked, root7Node145Step2Chunk2_2_checked, root7Node145Step2Chunk2_3_checked, root7Node145Step2Chunk2_4_checked, root7Node145Step2Chunk2_5_checked, root7Node145Step2Chunk3_0_checked, root7Node145Step2Chunk3_1_checked, root7Node145Step2Chunk3_2_checked, root7Node145Step2Chunk3_3_checked, root7Node145Step2Chunk3_4_checked, root7Node145Step2Chunk3_5_checked, root7Node145Step2Chunk4_0_checked, root7Node145Step2Chunk4_1_checked, root7Node145Step2Chunk4_2_checked, root7Node145Step2Chunk4_3_checked, root7Node145Step2Chunk4_4_checked, root7Node145Step2Chunk4_5_checked, root7Node145Step2Chunk5_0_checked, root7Node145Step2Chunk5_1_checked, root7Node145Step2Chunk5_2_checked, root7Node145Step2Chunk5_3_checked, root7Node145Step2Chunk5_4_checked, root7Node145Step2Chunk5_5_checked, root7Node145Step2Chunk6_0_checked, root7Node145Step2Chunk6_1_checked, root7Node145Step2Chunk6_2_checked, root7Node145Step2Chunk6_3_checked, root7Node145Step2Chunk6_4_checked, root7Node145Step2Chunk6_5_checked, root7Node145Step2Chunk7_0_checked, root7Node145Step2Chunk7_1_checked, root7Node145Step2Chunk7_2_checked, root7Node145Step2Chunk7_3_checked, root7Node145Step2Chunk7_4_checked, root7Node145Step2Chunk7_5_checked, root7Node145Step2Chunk8_0_checked, root7Node145Step2Chunk8_1_checked, root7Node145Step2Chunk8_2_checked, root7Node145Step2Chunk8_3_checked, root7Node145Step2Chunk8_4_checked, root7Node145Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node145Step2_checked :
    checkReplacement table56 root7Node145Domains1 root7Node145Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node145Domains1 root7Node145Domains2
    root7Node145Domains1Fast root7Node145Domains2Fast
    root7Node145Domains1_fast_eq root7Node145Domains2_fast_eq
    root7Node145Step2Narrowing_checked (by decide)
def root7Node146Domains0 : Domains 91 State := restrict root7Node145Domains2 20 (1,5)
def root7Node146Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
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
  | 20 => some [(1,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4)]
  | 59 => some [(1,3),(3,3),(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5)]
  | 66 => some [(0,2),(6,0)]
  | 67 => some [(1,1),(3,1),(7,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2),(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0),(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node146Domains0_fast_eq : root7Node146Domains0 = expandDomains root7Node146Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node146Domains0 v = expandDomains root7Node146Domains0Fast v from by decide) v
def root7Node146Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
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
  | 20 => [(1,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(7,0)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(5,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(2,0)]
  | 59 => [(7,3)]
  | 60 => [(5,2)]
  | 61 => [(1,1),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(3,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(1,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node146Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
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
  | 20 => some [(1,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(7,0)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(2,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(3,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node146Domains1_fast_eq : root7Node146Domains1 = expandDomains root7Node146Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node146Domains1 v = expandDomains root7Node146Domains1Fast v from by decide) v
theorem root7Node146Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq (by decide)
theorem root7Node146Step1Narrowing_checked :
    checkNarrowing table46 root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkNarrowing_flatten table46Scope [table46Rows0_0,table46Rows0_1,table46Rows0_2,table46Rows0_3,table46Rows0_4,table46Rows0_5,table46Rows1_0,table46Rows1_1,table46Rows1_2,table46Rows1_3,table46Rows1_4,table46Rows1_5,table46Rows2_0,table46Rows2_1,table46Rows2_2,table46Rows2_3,table46Rows2_4,table46Rows2_5,table46Rows3_0,table46Rows3_1,table46Rows3_2,table46Rows3_3,table46Rows3_4,table46Rows3_5,table46Rows4_0,table46Rows4_1,table46Rows4_2,table46Rows4_3,table46Rows4_4,table46Rows4_5,table46Rows5_0,table46Rows5_1,table46Rows5_2,table46Rows5_3,table46Rows5_4,table46Rows5_5,table46Rows6_0,table46Rows6_1,table46Rows6_2,table46Rows6_3,table46Rows6_4,table46Rows6_5,table46Rows7_0,table46Rows7_1,table46Rows7_2,table46Rows7_3,table46Rows7_4,table46Rows7_5,table46Rows8_0,table46Rows8_1,table46Rows8_2,table46Rows8_3,table46Rows8_4,table46Rows8_5]
    root7Node146Domains0 root7Node146Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node146Step1Chunk0_0_checked, root7Node146Step1Chunk0_1_checked, root7Node146Step1Chunk0_2_checked, root7Node146Step1Chunk0_3_checked, root7Node146Step1Chunk0_4_checked, root7Node146Step1Chunk0_5_checked, root7Node146Step1Chunk1_0_checked, root7Node146Step1Chunk1_1_checked, root7Node146Step1Chunk1_2_checked, root7Node146Step1Chunk1_3_checked, root7Node146Step1Chunk1_4_checked, root7Node146Step1Chunk1_5_checked, root7Node146Step1Chunk2_0_checked, root7Node146Step1Chunk2_1_checked, root7Node146Step1Chunk2_2_checked, root7Node146Step1Chunk2_3_checked, root7Node146Step1Chunk2_4_checked, root7Node146Step1Chunk2_5_checked, root7Node146Step1Chunk3_0_checked, root7Node146Step1Chunk3_1_checked, root7Node146Step1Chunk3_2_checked, root7Node146Step1Chunk3_3_checked, root7Node146Step1Chunk3_4_checked, root7Node146Step1Chunk3_5_checked, root7Node146Step1Chunk4_0_checked, root7Node146Step1Chunk4_1_checked, root7Node146Step1Chunk4_2_checked, root7Node146Step1Chunk4_3_checked, root7Node146Step1Chunk4_4_checked, root7Node146Step1Chunk4_5_checked, root7Node146Step1Chunk5_0_checked, root7Node146Step1Chunk5_1_checked, root7Node146Step1Chunk5_2_checked, root7Node146Step1Chunk5_3_checked, root7Node146Step1Chunk5_4_checked, root7Node146Step1Chunk5_5_checked, root7Node146Step1Chunk6_0_checked, root7Node146Step1Chunk6_1_checked, root7Node146Step1Chunk6_2_checked, root7Node146Step1Chunk6_3_checked, root7Node146Step1Chunk6_4_checked, root7Node146Step1Chunk6_5_checked, root7Node146Step1Chunk7_0_checked, root7Node146Step1Chunk7_1_checked, root7Node146Step1Chunk7_2_checked, root7Node146Step1Chunk7_3_checked, root7Node146Step1Chunk7_4_checked, root7Node146Step1Chunk7_5_checked, root7Node146Step1Chunk8_0_checked, root7Node146Step1Chunk8_1_checked, root7Node146Step1Chunk8_2_checked, root7Node146Step1Chunk8_3_checked, root7Node146Step1Chunk8_4_checked, root7Node146Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node146Step1_checked :
    checkReplacement table46 root7Node146Domains0 root7Node146Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node146Domains0 root7Node146Domains1
    root7Node146Domains0Fast root7Node146Domains1Fast
    root7Node146Domains0_fast_eq root7Node146Domains1_fast_eq
    root7Node146Step1Narrowing_checked (by decide)
def root7Node146Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
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
  | 20 => [(1,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(7,0)]
  | 30 => [(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(5,3)]
  | 41 => [(5,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,5)]
  | 52 => [(4,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(2,0)]
  | 59 => [(7,3)]
  | 60 => [(5,2)]
  | 61 => [(7,1)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(3,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(7,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(1,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node146Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
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
  | 20 => some [(1,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(7,0)]
  | 30 => some [(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,3)]
  | 41 => some [(5,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,5)]
  | 52 => some [(4,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(2,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(3,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node146Domains2_fast_eq : root7Node146Domains2 = expandDomains root7Node146Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node146Domains2 v = expandDomains root7Node146Domains2Fast v from by decide) v
theorem root7Node146Step2Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq (by decide)
theorem root7Node146Step2Narrowing_checked :
    checkNarrowing table30 root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkNarrowing_flatten table30Scope [table30Rows0_0,table30Rows0_1,table30Rows0_2,table30Rows0_3,table30Rows0_4,table30Rows0_5,table30Rows1_0,table30Rows1_1,table30Rows1_2,table30Rows1_3,table30Rows1_4,table30Rows1_5,table30Rows2_0,table30Rows2_1,table30Rows2_2,table30Rows2_3,table30Rows2_4,table30Rows2_5,table30Rows3_0,table30Rows3_1,table30Rows3_2,table30Rows3_3,table30Rows3_4,table30Rows3_5,table30Rows4_0,table30Rows4_1,table30Rows4_2,table30Rows4_3,table30Rows4_4,table30Rows4_5,table30Rows5_0,table30Rows5_1,table30Rows5_2,table30Rows5_3,table30Rows5_4,table30Rows5_5,table30Rows6_0,table30Rows6_1,table30Rows6_2,table30Rows6_3,table30Rows6_4,table30Rows6_5,table30Rows7_0,table30Rows7_1,table30Rows7_2,table30Rows7_3,table30Rows7_4,table30Rows7_5,table30Rows8_0,table30Rows8_1,table30Rows8_2,table30Rows8_3,table30Rows8_4,table30Rows8_5]
    root7Node146Domains1 root7Node146Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node146Step2Chunk0_0_checked, root7Node146Step2Chunk0_1_checked, root7Node146Step2Chunk0_2_checked, root7Node146Step2Chunk0_3_checked, root7Node146Step2Chunk0_4_checked, root7Node146Step2Chunk0_5_checked, root7Node146Step2Chunk1_0_checked, root7Node146Step2Chunk1_1_checked, root7Node146Step2Chunk1_2_checked, root7Node146Step2Chunk1_3_checked, root7Node146Step2Chunk1_4_checked, root7Node146Step2Chunk1_5_checked, root7Node146Step2Chunk2_0_checked, root7Node146Step2Chunk2_1_checked, root7Node146Step2Chunk2_2_checked, root7Node146Step2Chunk2_3_checked, root7Node146Step2Chunk2_4_checked, root7Node146Step2Chunk2_5_checked, root7Node146Step2Chunk3_0_checked, root7Node146Step2Chunk3_1_checked, root7Node146Step2Chunk3_2_checked, root7Node146Step2Chunk3_3_checked, root7Node146Step2Chunk3_4_checked, root7Node146Step2Chunk3_5_checked, root7Node146Step2Chunk4_0_checked, root7Node146Step2Chunk4_1_checked, root7Node146Step2Chunk4_2_checked, root7Node146Step2Chunk4_3_checked, root7Node146Step2Chunk4_4_checked, root7Node146Step2Chunk4_5_checked, root7Node146Step2Chunk5_0_checked, root7Node146Step2Chunk5_1_checked, root7Node146Step2Chunk5_2_checked, root7Node146Step2Chunk5_3_checked, root7Node146Step2Chunk5_4_checked, root7Node146Step2Chunk5_5_checked, root7Node146Step2Chunk6_0_checked, root7Node146Step2Chunk6_1_checked, root7Node146Step2Chunk6_2_checked, root7Node146Step2Chunk6_3_checked, root7Node146Step2Chunk6_4_checked, root7Node146Step2Chunk6_5_checked, root7Node146Step2Chunk7_0_checked, root7Node146Step2Chunk7_1_checked, root7Node146Step2Chunk7_2_checked, root7Node146Step2Chunk7_3_checked, root7Node146Step2Chunk7_4_checked, root7Node146Step2Chunk7_5_checked, root7Node146Step2Chunk8_0_checked, root7Node146Step2Chunk8_1_checked, root7Node146Step2Chunk8_2_checked, root7Node146Step2Chunk8_3_checked, root7Node146Step2Chunk8_4_checked, root7Node146Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node146Step2_checked :
    checkReplacement table30 root7Node146Domains1 root7Node146Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node146Domains1 root7Node146Domains2
    root7Node146Domains1Fast root7Node146Domains2Fast
    root7Node146Domains1_fast_eq root7Node146Domains2_fast_eq
    root7Node146Step2Narrowing_checked (by decide)
theorem root7Node146Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node146Domains2 (.output 71) = true := by decide
def root7Node147Domains0 : Domains 91 State := restrict root7Node145Domains2 20 (7,5)
def root7Node147Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
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
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4)]
  | 59 => some [(1,3),(3,3),(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5)]
  | 66 => some [(0,2),(6,0)]
  | 67 => some [(1,1),(3,1),(7,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2),(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0),(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node147Domains0_fast_eq : root7Node147Domains0 = expandDomains root7Node147Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node147Domains0 v = expandDomains root7Node147Domains0Fast v from by decide) v
def root7Node147Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
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
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(5,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(3,5),(7,5)]
  | 48 => [(0,3)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(6,3)]
  | 58 => [(2,2),(2,4)]
  | 59 => [(1,3),(3,3)]
  | 60 => [(5,2)]
  | 61 => [(1,1),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5)]
  | 66 => [(0,2),(6,0)]
  | 67 => [(1,1),(7,1)]
  | 68 => [(0,1),(6,5)]
  | 69 => [(0,4),(6,2)]
  | 70 => [(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(5,2),(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(1,0),(7,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node147Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
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
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(3,5),(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(2,2),(2,4)]
  | 59 => some [(1,3),(3,3)]
  | 60 => some [(5,2)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5)]
  | 66 => some [(0,2),(6,0)]
  | 67 => some [(1,1),(7,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2),(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0),(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node147Domains1_fast_eq : root7Node147Domains1 = expandDomains root7Node147Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node147Domains1 v = expandDomains root7Node147Domains1Fast v from by decide) v
theorem root7Node147Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq (by decide)
theorem root7Node147Step1Narrowing_checked :
    checkNarrowing table26 root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkNarrowing_flatten table26Scope [table26Rows0_0,table26Rows0_1,table26Rows0_2,table26Rows0_3,table26Rows0_4,table26Rows0_5,table26Rows1_0,table26Rows1_1,table26Rows1_2,table26Rows1_3,table26Rows1_4,table26Rows1_5,table26Rows2_0,table26Rows2_1,table26Rows2_2,table26Rows2_3,table26Rows2_4,table26Rows2_5,table26Rows3_0,table26Rows3_1,table26Rows3_2,table26Rows3_3,table26Rows3_4,table26Rows3_5,table26Rows4_0,table26Rows4_1,table26Rows4_2,table26Rows4_3,table26Rows4_4,table26Rows4_5,table26Rows5_0,table26Rows5_1,table26Rows5_2,table26Rows5_3,table26Rows5_4,table26Rows5_5,table26Rows6_0,table26Rows6_1,table26Rows6_2,table26Rows6_3,table26Rows6_4,table26Rows6_5,table26Rows7_0,table26Rows7_1,table26Rows7_2,table26Rows7_3,table26Rows7_4,table26Rows7_5,table26Rows8_0,table26Rows8_1,table26Rows8_2,table26Rows8_3,table26Rows8_4,table26Rows8_5]
    root7Node147Domains0 root7Node147Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node147Step1Chunk0_0_checked, root7Node147Step1Chunk0_1_checked, root7Node147Step1Chunk0_2_checked, root7Node147Step1Chunk0_3_checked, root7Node147Step1Chunk0_4_checked, root7Node147Step1Chunk0_5_checked, root7Node147Step1Chunk1_0_checked, root7Node147Step1Chunk1_1_checked, root7Node147Step1Chunk1_2_checked, root7Node147Step1Chunk1_3_checked, root7Node147Step1Chunk1_4_checked, root7Node147Step1Chunk1_5_checked, root7Node147Step1Chunk2_0_checked, root7Node147Step1Chunk2_1_checked, root7Node147Step1Chunk2_2_checked, root7Node147Step1Chunk2_3_checked, root7Node147Step1Chunk2_4_checked, root7Node147Step1Chunk2_5_checked, root7Node147Step1Chunk3_0_checked, root7Node147Step1Chunk3_1_checked, root7Node147Step1Chunk3_2_checked, root7Node147Step1Chunk3_3_checked, root7Node147Step1Chunk3_4_checked, root7Node147Step1Chunk3_5_checked, root7Node147Step1Chunk4_0_checked, root7Node147Step1Chunk4_1_checked, root7Node147Step1Chunk4_2_checked, root7Node147Step1Chunk4_3_checked, root7Node147Step1Chunk4_4_checked, root7Node147Step1Chunk4_5_checked, root7Node147Step1Chunk5_0_checked, root7Node147Step1Chunk5_1_checked, root7Node147Step1Chunk5_2_checked, root7Node147Step1Chunk5_3_checked, root7Node147Step1Chunk5_4_checked, root7Node147Step1Chunk5_5_checked, root7Node147Step1Chunk6_0_checked, root7Node147Step1Chunk6_1_checked, root7Node147Step1Chunk6_2_checked, root7Node147Step1Chunk6_3_checked, root7Node147Step1Chunk6_4_checked, root7Node147Step1Chunk6_5_checked, root7Node147Step1Chunk7_0_checked, root7Node147Step1Chunk7_1_checked, root7Node147Step1Chunk7_2_checked, root7Node147Step1Chunk7_3_checked, root7Node147Step1Chunk7_4_checked, root7Node147Step1Chunk7_5_checked, root7Node147Step1Chunk8_0_checked, root7Node147Step1Chunk8_1_checked, root7Node147Step1Chunk8_2_checked, root7Node147Step1Chunk8_3_checked, root7Node147Step1Chunk8_4_checked, root7Node147Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node147Step1_checked :
    checkReplacement table26 root7Node147Domains0 root7Node147Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node147Domains0 root7Node147Domains1
    root7Node147Domains0Fast root7Node147Domains1Fast
    root7Node147Domains0_fast_eq root7Node147Domains1_fast_eq
    root7Node147Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
