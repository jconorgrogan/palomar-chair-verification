module

public import SpectreFinite.RadiusFiveRoot5Part27
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable3
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node68Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(4,5),(7,3)]
  | 5 => [(4,2),(7,0)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1),(8,1)]
  | 10 => [(0,1),(6,5)]
  | 11 => [(0,4),(1,2),(6,2),(7,2)]
  | 12 => [(1,4),(7,4)]
  | 13 => [(5,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(1,0),(3,0)]
  | 19 => [(2,1),(2,5)]
  | 20 => [(0,2),(6,0)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2),(7,2)]
  | 29 => [(4,0),(8,0)]
  | 30 => [(2,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1),(1,4),(6,4)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(0,3),(1,0),(6,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(5,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root5Node68Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(4,2),(7,0)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(6,5)]
  | 11 => some [(0,4),(1,2),(6,2),(7,2)]
  | 12 => some [(1,4),(7,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(1,0),(3,0)]
  | 19 => some [(2,1),(2,5)]
  | 20 => some [(0,2),(6,0)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0),(8,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1),(1,4),(6,4)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(0,3),(1,0),(6,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(5,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root5Node68Domains2_fast_eq : root5Node68Domains2 = expandDomains root5Node68Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node68Domains2 v = expandDomains root5Node68Domains2Fast v from by decide) v
theorem root5Node68Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq (by decide)
theorem root5Node68Step2Narrowing_checked :
    checkNarrowing table56 root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root5Node68Domains1 root5Node68Domains2 (by
      simp only [List.all_cons, List.all_nil, root5Node68Step2Chunk0_0_checked, root5Node68Step2Chunk0_1_checked, root5Node68Step2Chunk0_2_checked, root5Node68Step2Chunk0_3_checked, root5Node68Step2Chunk0_4_checked, root5Node68Step2Chunk0_5_checked, root5Node68Step2Chunk1_0_checked, root5Node68Step2Chunk1_1_checked, root5Node68Step2Chunk1_2_checked, root5Node68Step2Chunk1_3_checked, root5Node68Step2Chunk1_4_checked, root5Node68Step2Chunk1_5_checked, root5Node68Step2Chunk2_0_checked, root5Node68Step2Chunk2_1_checked, root5Node68Step2Chunk2_2_checked, root5Node68Step2Chunk2_3_checked, root5Node68Step2Chunk2_4_checked, root5Node68Step2Chunk2_5_checked, root5Node68Step2Chunk3_0_checked, root5Node68Step2Chunk3_1_checked, root5Node68Step2Chunk3_2_checked, root5Node68Step2Chunk3_3_checked, root5Node68Step2Chunk3_4_checked, root5Node68Step2Chunk3_5_checked, root5Node68Step2Chunk4_0_checked, root5Node68Step2Chunk4_1_checked, root5Node68Step2Chunk4_2_checked, root5Node68Step2Chunk4_3_checked, root5Node68Step2Chunk4_4_checked, root5Node68Step2Chunk4_5_checked, root5Node68Step2Chunk5_0_checked, root5Node68Step2Chunk5_1_checked, root5Node68Step2Chunk5_2_checked, root5Node68Step2Chunk5_3_checked, root5Node68Step2Chunk5_4_checked, root5Node68Step2Chunk5_5_checked, root5Node68Step2Chunk6_0_checked, root5Node68Step2Chunk6_1_checked, root5Node68Step2Chunk6_2_checked, root5Node68Step2Chunk6_3_checked, root5Node68Step2Chunk6_4_checked, root5Node68Step2Chunk6_5_checked, root5Node68Step2Chunk7_0_checked, root5Node68Step2Chunk7_1_checked, root5Node68Step2Chunk7_2_checked, root5Node68Step2Chunk7_3_checked, root5Node68Step2Chunk7_4_checked, root5Node68Step2Chunk7_5_checked, root5Node68Step2Chunk8_0_checked, root5Node68Step2Chunk8_1_checked, root5Node68Step2Chunk8_2_checked, root5Node68Step2Chunk8_3_checked, root5Node68Step2Chunk8_4_checked, root5Node68Step2Chunk8_5_checked, Bool.true_and])
theorem root5Node68Step2_checked :
    checkReplacement table56 root5Node68Domains1 root5Node68Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root5Node68Domains1 root5Node68Domains2
    root5Node68Domains1Fast root5Node68Domains2Fast
    root5Node68Domains1_fast_eq root5Node68Domains2_fast_eq
    root5Node68Step2Narrowing_checked (by decide)
def root5Node68Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(7,3)]
  | 5 => [(4,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1),(8,1)]
  | 10 => [(0,1),(6,5)]
  | 11 => [(0,4),(6,2)]
  | 12 => [(1,4),(7,4)]
  | 13 => [(5,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(1,0),(3,0)]
  | 19 => [(2,1),(2,5)]
  | 20 => [(0,2),(6,0)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2),(7,2)]
  | 29 => [(4,0)]
  | 30 => [(2,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(5,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root5Node68Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(6,5)]
  | 11 => some [(0,4),(6,2)]
  | 12 => some [(1,4),(7,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(1,0),(3,0)]
  | 19 => some [(2,1),(2,5)]
  | 20 => some [(0,2),(6,0)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(5,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root5Node68Domains3_fast_eq : root5Node68Domains3 = expandDomains root5Node68Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node68Domains3 v = expandDomains root5Node68Domains3Fast v from by decide) v
theorem root5Node68Step3Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq (by decide)
theorem root5Node68Step3Narrowing_checked :
    checkNarrowing table12 root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root5Node68Domains2 root5Node68Domains3 (by
      simp only [List.all_cons, List.all_nil, root5Node68Step3Chunk0_0_checked, root5Node68Step3Chunk0_1_checked, root5Node68Step3Chunk0_2_checked, root5Node68Step3Chunk0_3_checked, root5Node68Step3Chunk0_4_checked, root5Node68Step3Chunk0_5_checked, root5Node68Step3Chunk1_0_checked, root5Node68Step3Chunk1_1_checked, root5Node68Step3Chunk1_2_checked, root5Node68Step3Chunk1_3_checked, root5Node68Step3Chunk1_4_checked, root5Node68Step3Chunk1_5_checked, root5Node68Step3Chunk2_0_checked, root5Node68Step3Chunk2_1_checked, root5Node68Step3Chunk2_2_checked, root5Node68Step3Chunk2_3_checked, root5Node68Step3Chunk2_4_checked, root5Node68Step3Chunk2_5_checked, root5Node68Step3Chunk3_0_checked, root5Node68Step3Chunk3_1_checked, root5Node68Step3Chunk3_2_checked, root5Node68Step3Chunk3_3_checked, root5Node68Step3Chunk3_4_checked, root5Node68Step3Chunk3_5_checked, root5Node68Step3Chunk4_0_checked, root5Node68Step3Chunk4_1_checked, root5Node68Step3Chunk4_2_checked, root5Node68Step3Chunk4_3_checked, root5Node68Step3Chunk4_4_checked, root5Node68Step3Chunk4_5_checked, root5Node68Step3Chunk5_0_checked, root5Node68Step3Chunk5_1_checked, root5Node68Step3Chunk5_2_checked, root5Node68Step3Chunk5_3_checked, root5Node68Step3Chunk5_4_checked, root5Node68Step3Chunk5_5_checked, root5Node68Step3Chunk6_0_checked, root5Node68Step3Chunk6_1_checked, root5Node68Step3Chunk6_2_checked, root5Node68Step3Chunk6_3_checked, root5Node68Step3Chunk6_4_checked, root5Node68Step3Chunk6_5_checked, root5Node68Step3Chunk7_0_checked, root5Node68Step3Chunk7_1_checked, root5Node68Step3Chunk7_2_checked, root5Node68Step3Chunk7_3_checked, root5Node68Step3Chunk7_4_checked, root5Node68Step3Chunk7_5_checked, root5Node68Step3Chunk8_0_checked, root5Node68Step3Chunk8_1_checked, root5Node68Step3Chunk8_2_checked, root5Node68Step3Chunk8_3_checked, root5Node68Step3Chunk8_4_checked, root5Node68Step3Chunk8_5_checked, Bool.true_and])
theorem root5Node68Step3_checked :
    checkReplacement table12 root5Node68Domains2 root5Node68Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root5Node68Domains2 root5Node68Domains3
    root5Node68Domains2Fast root5Node68Domains3Fast
    root5Node68Domains2_fast_eq root5Node68Domains3_fast_eq
    root5Node68Step3Narrowing_checked (by decide)
def root5Node68Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(7,3)]
  | 5 => [(4,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1),(8,1)]
  | 10 => [(0,1),(6,5)]
  | 11 => [(0,4),(6,2)]
  | 12 => [(1,4),(7,4)]
  | 13 => [(5,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(1,0),(3,0)]
  | 19 => [(2,1),(2,5)]
  | 20 => [(0,2),(6,0)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2),(7,2)]
  | 29 => [(4,0)]
  | 30 => [(2,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(4,3)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root5Node68Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(6,5)]
  | 11 => some [(0,4),(6,2)]
  | 12 => some [(1,4),(7,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(1,0),(3,0)]
  | 19 => some [(2,1),(2,5)]
  | 20 => some [(0,2),(6,0)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root5Node68Domains4_fast_eq : root5Node68Domains4 = expandDomains root5Node68Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node68Domains4 v = expandDomains root5Node68Domains4Fast v from by decide) v
theorem root5Node68Step4Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq (by decide)
theorem root5Node68Step4Narrowing_checked :
    checkNarrowing table51 root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root5Node68Domains3 root5Node68Domains4 (by
      simp only [List.all_cons, List.all_nil, root5Node68Step4Chunk0_0_checked, root5Node68Step4Chunk0_1_checked, root5Node68Step4Chunk0_2_checked, root5Node68Step4Chunk0_3_checked, root5Node68Step4Chunk0_4_checked, root5Node68Step4Chunk0_5_checked, root5Node68Step4Chunk1_0_checked, root5Node68Step4Chunk1_1_checked, root5Node68Step4Chunk1_2_checked, root5Node68Step4Chunk1_3_checked, root5Node68Step4Chunk1_4_checked, root5Node68Step4Chunk1_5_checked, root5Node68Step4Chunk2_0_checked, root5Node68Step4Chunk2_1_checked, root5Node68Step4Chunk2_2_checked, root5Node68Step4Chunk2_3_checked, root5Node68Step4Chunk2_4_checked, root5Node68Step4Chunk2_5_checked, root5Node68Step4Chunk3_0_checked, root5Node68Step4Chunk3_1_checked, root5Node68Step4Chunk3_2_checked, root5Node68Step4Chunk3_3_checked, root5Node68Step4Chunk3_4_checked, root5Node68Step4Chunk3_5_checked, root5Node68Step4Chunk4_0_checked, root5Node68Step4Chunk4_1_checked, root5Node68Step4Chunk4_2_checked, root5Node68Step4Chunk4_3_checked, root5Node68Step4Chunk4_4_checked, root5Node68Step4Chunk4_5_checked, root5Node68Step4Chunk5_0_checked, root5Node68Step4Chunk5_1_checked, root5Node68Step4Chunk5_2_checked, root5Node68Step4Chunk5_3_checked, root5Node68Step4Chunk5_4_checked, root5Node68Step4Chunk5_5_checked, root5Node68Step4Chunk6_0_checked, root5Node68Step4Chunk6_1_checked, root5Node68Step4Chunk6_2_checked, root5Node68Step4Chunk6_3_checked, root5Node68Step4Chunk6_4_checked, root5Node68Step4Chunk6_5_checked, root5Node68Step4Chunk7_0_checked, root5Node68Step4Chunk7_1_checked, root5Node68Step4Chunk7_2_checked, root5Node68Step4Chunk7_3_checked, root5Node68Step4Chunk7_4_checked, root5Node68Step4Chunk7_5_checked, root5Node68Step4Chunk8_0_checked, root5Node68Step4Chunk8_1_checked, root5Node68Step4Chunk8_2_checked, root5Node68Step4Chunk8_3_checked, root5Node68Step4Chunk8_4_checked, root5Node68Step4Chunk8_5_checked, Bool.true_and])
theorem root5Node68Step4_checked :
    checkReplacement table51 root5Node68Domains3 root5Node68Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root5Node68Domains3 root5Node68Domains4
    root5Node68Domains3Fast root5Node68Domains4Fast
    root5Node68Domains3_fast_eq root5Node68Domains4_fast_eq
    root5Node68Step4Narrowing_checked (by decide)
def root5Node69Domains0 : Domains 91 State := restrict root5Node68Domains4 3 (4,0)
def root5Node69Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(6,5)]
  | 11 => some [(0,4),(6,2)]
  | 12 => some [(1,4),(7,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(1,0),(3,0)]
  | 19 => some [(2,1),(2,5)]
  | 20 => some [(0,2),(6,0)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root5Node69Domains0_fast_eq : root5Node69Domains0 = expandDomains root5Node69Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node69Domains0 v = expandDomains root5Node69Domains0Fast v from by decide) v
def root5Node69Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(4,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(7,4)]
  | 13 => [(5,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1)]
  | 20 => [(0,2)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2)]
  | 29 => [(4,0)]
  | 30 => [(2,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(5,0)]
  | 73 => [(4,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(4,3)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root5Node69Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(7,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2)]
  | 29 => some [(4,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(5,0)]
  | 73 => some [(4,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root5Node69Domains1_fast_eq : root5Node69Domains1 = expandDomains root5Node69Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node69Domains1 v = expandDomains root5Node69Domains1Fast v from by decide) v
theorem root5Node69Step1Chunk0_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_0⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk0_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_1⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk0_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_2⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk0_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_3⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk0_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_4⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk0_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_5⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk1_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_0⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk1_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_1⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk1_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_2⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk1_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_3⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk1_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_4⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk1_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_5⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk2_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_0⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk2_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_1⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk2_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_2⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk2_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_3⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk2_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_4⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk2_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_5⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk3_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_0⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk3_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_1⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk3_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_2⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk3_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_3⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk3_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_4⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk3_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_5⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk4_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_0⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk4_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_1⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk4_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_2⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk4_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_3⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk4_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_4⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk4_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_5⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk5_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_0⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk5_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_1⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk5_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_2⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk5_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_3⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk5_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_4⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk5_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_5⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk6_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_0⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk6_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_1⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk6_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_2⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk6_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_3⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk6_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_4⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk6_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_5⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk7_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_0⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk7_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_1⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk7_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_2⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk7_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_3⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk7_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_4⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk7_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_5⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk8_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_0⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk8_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_1⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk8_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_2⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk8_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_3⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk8_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_4⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Chunk8_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_5⟩
      root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq (by decide)
theorem root5Node69Step1Narrowing_checked :
    checkNarrowing table3 root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkNarrowing_flatten table3Scope [table3Rows0_0,table3Rows0_1,table3Rows0_2,table3Rows0_3,table3Rows0_4,table3Rows0_5,table3Rows1_0,table3Rows1_1,table3Rows1_2,table3Rows1_3,table3Rows1_4,table3Rows1_5,table3Rows2_0,table3Rows2_1,table3Rows2_2,table3Rows2_3,table3Rows2_4,table3Rows2_5,table3Rows3_0,table3Rows3_1,table3Rows3_2,table3Rows3_3,table3Rows3_4,table3Rows3_5,table3Rows4_0,table3Rows4_1,table3Rows4_2,table3Rows4_3,table3Rows4_4,table3Rows4_5,table3Rows5_0,table3Rows5_1,table3Rows5_2,table3Rows5_3,table3Rows5_4,table3Rows5_5,table3Rows6_0,table3Rows6_1,table3Rows6_2,table3Rows6_3,table3Rows6_4,table3Rows6_5,table3Rows7_0,table3Rows7_1,table3Rows7_2,table3Rows7_3,table3Rows7_4,table3Rows7_5,table3Rows8_0,table3Rows8_1,table3Rows8_2,table3Rows8_3,table3Rows8_4,table3Rows8_5]
    root5Node69Domains0 root5Node69Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node69Step1Chunk0_0_checked, root5Node69Step1Chunk0_1_checked, root5Node69Step1Chunk0_2_checked, root5Node69Step1Chunk0_3_checked, root5Node69Step1Chunk0_4_checked, root5Node69Step1Chunk0_5_checked, root5Node69Step1Chunk1_0_checked, root5Node69Step1Chunk1_1_checked, root5Node69Step1Chunk1_2_checked, root5Node69Step1Chunk1_3_checked, root5Node69Step1Chunk1_4_checked, root5Node69Step1Chunk1_5_checked, root5Node69Step1Chunk2_0_checked, root5Node69Step1Chunk2_1_checked, root5Node69Step1Chunk2_2_checked, root5Node69Step1Chunk2_3_checked, root5Node69Step1Chunk2_4_checked, root5Node69Step1Chunk2_5_checked, root5Node69Step1Chunk3_0_checked, root5Node69Step1Chunk3_1_checked, root5Node69Step1Chunk3_2_checked, root5Node69Step1Chunk3_3_checked, root5Node69Step1Chunk3_4_checked, root5Node69Step1Chunk3_5_checked, root5Node69Step1Chunk4_0_checked, root5Node69Step1Chunk4_1_checked, root5Node69Step1Chunk4_2_checked, root5Node69Step1Chunk4_3_checked, root5Node69Step1Chunk4_4_checked, root5Node69Step1Chunk4_5_checked, root5Node69Step1Chunk5_0_checked, root5Node69Step1Chunk5_1_checked, root5Node69Step1Chunk5_2_checked, root5Node69Step1Chunk5_3_checked, root5Node69Step1Chunk5_4_checked, root5Node69Step1Chunk5_5_checked, root5Node69Step1Chunk6_0_checked, root5Node69Step1Chunk6_1_checked, root5Node69Step1Chunk6_2_checked, root5Node69Step1Chunk6_3_checked, root5Node69Step1Chunk6_4_checked, root5Node69Step1Chunk6_5_checked, root5Node69Step1Chunk7_0_checked, root5Node69Step1Chunk7_1_checked, root5Node69Step1Chunk7_2_checked, root5Node69Step1Chunk7_3_checked, root5Node69Step1Chunk7_4_checked, root5Node69Step1Chunk7_5_checked, root5Node69Step1Chunk8_0_checked, root5Node69Step1Chunk8_1_checked, root5Node69Step1Chunk8_2_checked, root5Node69Step1Chunk8_3_checked, root5Node69Step1Chunk8_4_checked, root5Node69Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node69Step1_checked :
    checkReplacement table3 root5Node69Domains0 root5Node69Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node69Domains0 root5Node69Domains1
    root5Node69Domains0Fast root5Node69Domains1Fast
    root5Node69Domains0_fast_eq root5Node69Domains1_fast_eq
    root5Node69Step1Narrowing_checked (by decide)
theorem root5Node69Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node69Domains1 (.output 34) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
