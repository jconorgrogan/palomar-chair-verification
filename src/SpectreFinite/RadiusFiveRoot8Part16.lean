module

public import SpectreFinite.RadiusFiveRoot8Part15
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable5
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node37Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4),(8,4)]
  | 4 => [(0,0),(1,3),(7,3)]
  | 5 => [(7,2),(8,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5),(6,5)]
  | 11 => [(0,4),(6,1),(6,2)]
  | 12 => [(5,1),(5,4),(8,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3),(6,3)]
  | 29 => [(2,2),(4,2),(8,2)]
  | 30 => [(4,3)]
  | 31 => [(3,5),(7,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1),(8,1)]
  | 37 => [(0,2),(6,5)]
  | 38 => [(0,4),(1,1)]
  | 39 => [(0,1),(1,4),(3,4),(5,4),(7,4)]
  | 40 => [(1,4),(7,4)]
  | 41 => [(0,5),(6,3)]
  | 42 => [(2,2),(2,4)]
  | 43 => [(1,3),(3,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(3,0),(5,0),(7,0)]
  | 49 => [(2,3),(2,5),(4,3),(4,5)]
  | 50 => [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => [(0,2),(6,0)]
  | 52 => [(1,1),(7,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0),(1,4),(6,4)]
  | 60 => [(0,5),(1,2),(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3),(6,0)]
  | 67 => [(7,1),(8,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,0),(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0),(7,4)]
  | 73 => [(1,3),(7,3)]
  | 74 => [(4,2),(8,2)]
  | 75 => [(5,0),(5,3),(8,0)]
  | 76 => [(4,5),(5,5),(7,3),(8,5)]
  | 77 => [(4,2),(7,0),(8,2)]
  | 78 => [(0,4),(1,1),(6,1)]
  | 79 => [(5,1),(8,1)]
  | 80 => [(0,1),(6,5)]
  | 81 => [(0,4),(6,2)]
  | 82 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => [(0,0),(0,5),(6,3),(6,4)]
  | 84 => [(1,2),(4,4),(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(5,5),(8,5)]
  | 87 => [(1,0),(3,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 89 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => [(0,3),(1,1),(6,1),(7,1)]
def root8Node37Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4),(8,4)]
  | 4 => some [(0,0),(1,3),(7,3)]
  | 5 => some [(7,2),(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5),(6,5)]
  | 11 => some [(0,4),(6,1),(6,2)]
  | 12 => some [(5,1),(5,4),(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3),(6,3)]
  | 29 => some [(2,2),(4,2),(8,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5),(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(8,1)]
  | 37 => some [(0,2),(6,5)]
  | 38 => some [(0,4),(1,1)]
  | 39 => some [(0,1),(1,4),(3,4),(5,4),(7,4)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(0,5),(6,3)]
  | 42 => some [(2,2),(2,4)]
  | 43 => some [(1,3),(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(3,0),(5,0),(7,0)]
  | 49 => some [(2,3),(2,5),(4,3),(4,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => some [(0,2),(6,0)]
  | 52 => some [(1,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,0),(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0),(7,4)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(5,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0),(8,2)]
  | 78 => some [(0,4),(1,1),(6,1)]
  | 79 => some [(5,1),(8,1)]
  | 80 => some [(0,1),(6,5)]
  | 81 => some [(0,4),(6,2)]
  | 82 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => some [(0,0),(0,5),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 89 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => some [(0,3),(1,1),(6,1),(7,1)]
theorem root8Node37Domains2_fast_eq : root8Node37Domains2 = expandDomains root8Node37Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node37Domains2 v = expandDomains root8Node37Domains2Fast v from by decide) v
theorem root8Node37Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq (by decide)
theorem root8Node37Step2Narrowing_checked :
    checkNarrowing table56 root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root8Node37Domains1 root8Node37Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node37Step2Chunk0_0_checked, root8Node37Step2Chunk0_1_checked, root8Node37Step2Chunk0_2_checked, root8Node37Step2Chunk0_3_checked, root8Node37Step2Chunk0_4_checked, root8Node37Step2Chunk0_5_checked, root8Node37Step2Chunk1_0_checked, root8Node37Step2Chunk1_1_checked, root8Node37Step2Chunk1_2_checked, root8Node37Step2Chunk1_3_checked, root8Node37Step2Chunk1_4_checked, root8Node37Step2Chunk1_5_checked, root8Node37Step2Chunk2_0_checked, root8Node37Step2Chunk2_1_checked, root8Node37Step2Chunk2_2_checked, root8Node37Step2Chunk2_3_checked, root8Node37Step2Chunk2_4_checked, root8Node37Step2Chunk2_5_checked, root8Node37Step2Chunk3_0_checked, root8Node37Step2Chunk3_1_checked, root8Node37Step2Chunk3_2_checked, root8Node37Step2Chunk3_3_checked, root8Node37Step2Chunk3_4_checked, root8Node37Step2Chunk3_5_checked, root8Node37Step2Chunk4_0_checked, root8Node37Step2Chunk4_1_checked, root8Node37Step2Chunk4_2_checked, root8Node37Step2Chunk4_3_checked, root8Node37Step2Chunk4_4_checked, root8Node37Step2Chunk4_5_checked, root8Node37Step2Chunk5_0_checked, root8Node37Step2Chunk5_1_checked, root8Node37Step2Chunk5_2_checked, root8Node37Step2Chunk5_3_checked, root8Node37Step2Chunk5_4_checked, root8Node37Step2Chunk5_5_checked, root8Node37Step2Chunk6_0_checked, root8Node37Step2Chunk6_1_checked, root8Node37Step2Chunk6_2_checked, root8Node37Step2Chunk6_3_checked, root8Node37Step2Chunk6_4_checked, root8Node37Step2Chunk6_5_checked, root8Node37Step2Chunk7_0_checked, root8Node37Step2Chunk7_1_checked, root8Node37Step2Chunk7_2_checked, root8Node37Step2Chunk7_3_checked, root8Node37Step2Chunk7_4_checked, root8Node37Step2Chunk7_5_checked, root8Node37Step2Chunk8_0_checked, root8Node37Step2Chunk8_1_checked, root8Node37Step2Chunk8_2_checked, root8Node37Step2Chunk8_3_checked, root8Node37Step2Chunk8_4_checked, root8Node37Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node37Step2_checked :
    checkReplacement table56 root8Node37Domains1 root8Node37Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node37Domains1 root8Node37Domains2
    root8Node37Domains1Fast root8Node37Domains2Fast
    root8Node37Domains1_fast_eq root8Node37Domains2_fast_eq
    root8Node37Step2Narrowing_checked (by decide)
def root8Node37Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4),(8,4)]
  | 4 => [(0,0),(1,3)]
  | 5 => [(7,2),(8,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5),(6,5)]
  | 11 => [(0,4),(6,1)]
  | 12 => [(5,1),(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3),(6,3)]
  | 29 => [(2,2),(4,2),(8,2)]
  | 30 => [(4,3)]
  | 31 => [(3,5),(7,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1),(8,1)]
  | 37 => [(0,2),(6,5)]
  | 38 => [(0,4),(1,1)]
  | 39 => [(0,1),(1,4),(3,4),(5,4)]
  | 40 => [(1,4),(7,4)]
  | 41 => [(0,5),(6,3)]
  | 42 => [(2,2),(2,4)]
  | 43 => [(1,3),(3,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(3,0),(5,0),(7,0)]
  | 49 => [(2,3),(2,5),(4,3),(4,5)]
  | 50 => [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => [(0,2),(6,0)]
  | 52 => [(1,1),(7,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0),(1,4),(6,4)]
  | 60 => [(0,5),(1,2),(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3),(6,0)]
  | 67 => [(7,1),(8,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,0),(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0),(7,4)]
  | 73 => [(1,3),(7,3)]
  | 74 => [(4,2),(8,2)]
  | 75 => [(5,0),(5,3),(8,0)]
  | 76 => [(4,5),(5,5),(7,3),(8,5)]
  | 77 => [(4,2),(7,0),(8,2)]
  | 78 => [(0,4),(1,1),(6,1)]
  | 79 => [(5,1),(8,1)]
  | 80 => [(0,1),(6,5)]
  | 81 => [(0,4),(6,2)]
  | 82 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => [(0,0),(0,5),(6,3),(6,4)]
  | 84 => [(1,2),(4,4),(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(5,5),(8,5)]
  | 87 => [(1,0),(3,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 89 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => [(0,3),(1,1),(6,1),(7,1)]
def root8Node37Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4),(8,4)]
  | 4 => some [(0,0),(1,3)]
  | 5 => some [(7,2),(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5),(6,5)]
  | 11 => some [(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3),(6,3)]
  | 29 => some [(2,2),(4,2),(8,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5),(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(8,1)]
  | 37 => some [(0,2),(6,5)]
  | 38 => some [(0,4),(1,1)]
  | 39 => some [(0,1),(1,4),(3,4),(5,4)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(0,5),(6,3)]
  | 42 => some [(2,2),(2,4)]
  | 43 => some [(1,3),(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(3,0),(5,0),(7,0)]
  | 49 => some [(2,3),(2,5),(4,3),(4,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => some [(0,2),(6,0)]
  | 52 => some [(1,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,0),(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0),(7,4)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(5,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0),(8,2)]
  | 78 => some [(0,4),(1,1),(6,1)]
  | 79 => some [(5,1),(8,1)]
  | 80 => some [(0,1),(6,5)]
  | 81 => some [(0,4),(6,2)]
  | 82 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => some [(0,0),(0,5),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 89 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => some [(0,3),(1,1),(6,1),(7,1)]
theorem root8Node37Domains3_fast_eq : root8Node37Domains3 = expandDomains root8Node37Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node37Domains3 v = expandDomains root8Node37Domains3Fast v from by decide) v
theorem root8Node37Step3Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq (by decide)
theorem root8Node37Step3Narrowing_checked :
    checkNarrowing table5 root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkNarrowing_flatten table5Scope [table5Rows0_0,table5Rows0_1,table5Rows0_2,table5Rows0_3,table5Rows0_4,table5Rows0_5,table5Rows1_0,table5Rows1_1,table5Rows1_2,table5Rows1_3,table5Rows1_4,table5Rows1_5,table5Rows2_0,table5Rows2_1,table5Rows2_2,table5Rows2_3,table5Rows2_4,table5Rows2_5,table5Rows3_0,table5Rows3_1,table5Rows3_2,table5Rows3_3,table5Rows3_4,table5Rows3_5,table5Rows4_0,table5Rows4_1,table5Rows4_2,table5Rows4_3,table5Rows4_4,table5Rows4_5,table5Rows5_0,table5Rows5_1,table5Rows5_2,table5Rows5_3,table5Rows5_4,table5Rows5_5,table5Rows6_0,table5Rows6_1,table5Rows6_2,table5Rows6_3,table5Rows6_4,table5Rows6_5,table5Rows7_0,table5Rows7_1,table5Rows7_2,table5Rows7_3,table5Rows7_4,table5Rows7_5,table5Rows8_0,table5Rows8_1,table5Rows8_2,table5Rows8_3,table5Rows8_4,table5Rows8_5]
    root8Node37Domains2 root8Node37Domains3 (by
      simp only [List.all_cons, List.all_nil, root8Node37Step3Chunk0_0_checked, root8Node37Step3Chunk0_1_checked, root8Node37Step3Chunk0_2_checked, root8Node37Step3Chunk0_3_checked, root8Node37Step3Chunk0_4_checked, root8Node37Step3Chunk0_5_checked, root8Node37Step3Chunk1_0_checked, root8Node37Step3Chunk1_1_checked, root8Node37Step3Chunk1_2_checked, root8Node37Step3Chunk1_3_checked, root8Node37Step3Chunk1_4_checked, root8Node37Step3Chunk1_5_checked, root8Node37Step3Chunk2_0_checked, root8Node37Step3Chunk2_1_checked, root8Node37Step3Chunk2_2_checked, root8Node37Step3Chunk2_3_checked, root8Node37Step3Chunk2_4_checked, root8Node37Step3Chunk2_5_checked, root8Node37Step3Chunk3_0_checked, root8Node37Step3Chunk3_1_checked, root8Node37Step3Chunk3_2_checked, root8Node37Step3Chunk3_3_checked, root8Node37Step3Chunk3_4_checked, root8Node37Step3Chunk3_5_checked, root8Node37Step3Chunk4_0_checked, root8Node37Step3Chunk4_1_checked, root8Node37Step3Chunk4_2_checked, root8Node37Step3Chunk4_3_checked, root8Node37Step3Chunk4_4_checked, root8Node37Step3Chunk4_5_checked, root8Node37Step3Chunk5_0_checked, root8Node37Step3Chunk5_1_checked, root8Node37Step3Chunk5_2_checked, root8Node37Step3Chunk5_3_checked, root8Node37Step3Chunk5_4_checked, root8Node37Step3Chunk5_5_checked, root8Node37Step3Chunk6_0_checked, root8Node37Step3Chunk6_1_checked, root8Node37Step3Chunk6_2_checked, root8Node37Step3Chunk6_3_checked, root8Node37Step3Chunk6_4_checked, root8Node37Step3Chunk6_5_checked, root8Node37Step3Chunk7_0_checked, root8Node37Step3Chunk7_1_checked, root8Node37Step3Chunk7_2_checked, root8Node37Step3Chunk7_3_checked, root8Node37Step3Chunk7_4_checked, root8Node37Step3Chunk7_5_checked, root8Node37Step3Chunk8_0_checked, root8Node37Step3Chunk8_1_checked, root8Node37Step3Chunk8_2_checked, root8Node37Step3Chunk8_3_checked, root8Node37Step3Chunk8_4_checked, root8Node37Step3Chunk8_5_checked, Bool.true_and])
theorem root8Node37Step3_checked :
    checkReplacement table5 root8Node37Domains2 root8Node37Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root8Node37Domains2 root8Node37Domains3
    root8Node37Domains2Fast root8Node37Domains3Fast
    root8Node37Domains2_fast_eq root8Node37Domains3_fast_eq
    root8Node37Step3Narrowing_checked (by decide)
def root8Node37Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4),(8,4)]
  | 4 => [(0,0),(1,3)]
  | 5 => [(7,2),(8,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5),(6,5)]
  | 11 => [(0,4),(6,1)]
  | 12 => [(5,1),(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3),(6,3)]
  | 29 => [(2,2),(4,2),(8,2)]
  | 30 => [(4,3)]
  | 31 => [(3,5),(7,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1),(8,1)]
  | 37 => [(0,2),(6,5)]
  | 38 => [(0,4),(1,1)]
  | 39 => [(0,1),(1,4),(3,4),(5,4)]
  | 40 => [(1,4),(7,4)]
  | 41 => [(0,5),(6,3)]
  | 42 => [(2,2),(2,4)]
  | 43 => [(1,3),(3,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(3,0),(5,0),(7,0)]
  | 49 => [(2,3),(2,5),(4,3),(4,5)]
  | 50 => [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => [(0,2),(6,0)]
  | 52 => [(1,1),(7,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0),(1,4),(6,4)]
  | 60 => [(0,5),(1,2),(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3),(6,0)]
  | 67 => [(7,1),(8,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,0),(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0),(7,4)]
  | 73 => [(1,3),(7,3)]
  | 74 => [(4,2),(8,2)]
  | 75 => [(5,0),(5,3),(8,0)]
  | 76 => [(4,5),(5,5),(7,3),(8,5)]
  | 77 => [(4,2),(7,0),(8,2)]
  | 78 => [(6,1)]
  | 79 => [(5,1),(8,1)]
  | 80 => [(0,1),(6,5)]
  | 81 => [(0,4),(6,2)]
  | 82 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => [(0,0),(0,5),(6,3),(6,4)]
  | 84 => [(1,2),(4,4),(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5),(8,5)]
  | 87 => [(1,0),(3,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 89 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => [(0,3),(1,1),(6,1),(7,1)]
def root8Node37Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4),(8,4)]
  | 4 => some [(0,0),(1,3)]
  | 5 => some [(7,2),(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5),(6,5)]
  | 11 => some [(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3),(6,3)]
  | 29 => some [(2,2),(4,2),(8,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5),(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(8,1)]
  | 37 => some [(0,2),(6,5)]
  | 38 => some [(0,4),(1,1)]
  | 39 => some [(0,1),(1,4),(3,4),(5,4)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(0,5),(6,3)]
  | 42 => some [(2,2),(2,4)]
  | 43 => some [(1,3),(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(3,0),(5,0),(7,0)]
  | 49 => some [(2,3),(2,5),(4,3),(4,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => some [(0,2),(6,0)]
  | 52 => some [(1,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,0),(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0),(7,4)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(5,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0),(8,2)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1),(8,1)]
  | 80 => some [(0,1),(6,5)]
  | 81 => some [(0,4),(6,2)]
  | 82 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => some [(0,0),(0,5),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 89 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => some [(0,3),(1,1),(6,1),(7,1)]
theorem root8Node37Domains4_fast_eq : root8Node37Domains4 = expandDomains root8Node37Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node37Domains4 v = expandDomains root8Node37Domains4Fast v from by decide) v
theorem root8Node37Step4Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq (by decide)
theorem root8Node37Step4Narrowing_checked :
    checkNarrowing table51 root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root8Node37Domains3 root8Node37Domains4 (by
      simp only [List.all_cons, List.all_nil, root8Node37Step4Chunk0_0_checked, root8Node37Step4Chunk0_1_checked, root8Node37Step4Chunk0_2_checked, root8Node37Step4Chunk0_3_checked, root8Node37Step4Chunk0_4_checked, root8Node37Step4Chunk0_5_checked, root8Node37Step4Chunk1_0_checked, root8Node37Step4Chunk1_1_checked, root8Node37Step4Chunk1_2_checked, root8Node37Step4Chunk1_3_checked, root8Node37Step4Chunk1_4_checked, root8Node37Step4Chunk1_5_checked, root8Node37Step4Chunk2_0_checked, root8Node37Step4Chunk2_1_checked, root8Node37Step4Chunk2_2_checked, root8Node37Step4Chunk2_3_checked, root8Node37Step4Chunk2_4_checked, root8Node37Step4Chunk2_5_checked, root8Node37Step4Chunk3_0_checked, root8Node37Step4Chunk3_1_checked, root8Node37Step4Chunk3_2_checked, root8Node37Step4Chunk3_3_checked, root8Node37Step4Chunk3_4_checked, root8Node37Step4Chunk3_5_checked, root8Node37Step4Chunk4_0_checked, root8Node37Step4Chunk4_1_checked, root8Node37Step4Chunk4_2_checked, root8Node37Step4Chunk4_3_checked, root8Node37Step4Chunk4_4_checked, root8Node37Step4Chunk4_5_checked, root8Node37Step4Chunk5_0_checked, root8Node37Step4Chunk5_1_checked, root8Node37Step4Chunk5_2_checked, root8Node37Step4Chunk5_3_checked, root8Node37Step4Chunk5_4_checked, root8Node37Step4Chunk5_5_checked, root8Node37Step4Chunk6_0_checked, root8Node37Step4Chunk6_1_checked, root8Node37Step4Chunk6_2_checked, root8Node37Step4Chunk6_3_checked, root8Node37Step4Chunk6_4_checked, root8Node37Step4Chunk6_5_checked, root8Node37Step4Chunk7_0_checked, root8Node37Step4Chunk7_1_checked, root8Node37Step4Chunk7_2_checked, root8Node37Step4Chunk7_3_checked, root8Node37Step4Chunk7_4_checked, root8Node37Step4Chunk7_5_checked, root8Node37Step4Chunk8_0_checked, root8Node37Step4Chunk8_1_checked, root8Node37Step4Chunk8_2_checked, root8Node37Step4Chunk8_3_checked, root8Node37Step4Chunk8_4_checked, root8Node37Step4Chunk8_5_checked, Bool.true_and])
theorem root8Node37Step4_checked :
    checkReplacement table51 root8Node37Domains3 root8Node37Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root8Node37Domains3 root8Node37Domains4
    root8Node37Domains3Fast root8Node37Domains4Fast
    root8Node37Domains3_fast_eq root8Node37Domains4_fast_eq
    root8Node37Step4Narrowing_checked (by decide)
def root8Node38Domains0 : Domains 91 State := restrict root8Node37Domains4 3 (7,4)
def root8Node38Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(0,0),(1,3)]
  | 5 => some [(7,2),(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5),(6,5)]
  | 11 => some [(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3),(6,3)]
  | 29 => some [(2,2),(4,2),(8,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5),(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(8,1)]
  | 37 => some [(0,2),(6,5)]
  | 38 => some [(0,4),(1,1)]
  | 39 => some [(0,1),(1,4),(3,4),(5,4)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(0,5),(6,3)]
  | 42 => some [(2,2),(2,4)]
  | 43 => some [(1,3),(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(3,0),(5,0),(7,0)]
  | 49 => some [(2,3),(2,5),(4,3),(4,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => some [(0,2),(6,0)]
  | 52 => some [(1,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,0),(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0),(7,4)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(5,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0),(8,2)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1),(8,1)]
  | 80 => some [(0,1),(6,5)]
  | 81 => some [(0,4),(6,2)]
  | 82 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => some [(0,0),(0,5),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 89 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => some [(0,3),(1,1),(6,1),(7,1)]
theorem root8Node38Domains0_fast_eq : root8Node38Domains0 = expandDomains root8Node38Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node38Domains0 v = expandDomains root8Node38Domains0Fast v from by decide) v
def root8Node38Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3),(6,3)]
  | 29 => [(2,2),(4,2)]
  | 30 => [(4,3)]
  | 31 => [(3,5),(7,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1),(8,1)]
  | 37 => [(0,2),(6,5)]
  | 38 => [(0,4),(1,1)]
  | 39 => [(0,1),(1,4),(3,4)]
  | 40 => [(1,4),(7,4)]
  | 41 => [(0,5),(6,3)]
  | 42 => [(2,2),(2,4)]
  | 43 => [(1,3),(3,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(3,0),(5,0),(7,0)]
  | 49 => [(2,3),(2,5),(4,5)]
  | 50 => [(0,2),(1,0),(6,0)]
  | 51 => [(0,2),(6,0)]
  | 52 => [(1,1),(7,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0),(6,4)]
  | 60 => [(1,2),(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3),(6,0)]
  | 67 => [(7,1),(8,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0),(7,4)]
  | 73 => [(1,3),(7,3)]
  | 74 => [(4,2),(8,2)]
  | 75 => [(5,0),(5,3),(8,0)]
  | 76 => [(4,5),(5,5),(7,3),(8,5)]
  | 77 => [(4,2),(7,0)]
  | 78 => [(6,1)]
  | 79 => [(5,1),(8,1)]
  | 80 => [(0,1),(6,5)]
  | 81 => [(0,4),(6,2)]
  | 82 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => [(0,0),(0,5),(6,3),(6,4)]
  | 84 => [(1,2),(4,4),(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5),(8,5)]
  | 87 => [(1,0),(3,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 89 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => [(0,3),(1,1),(6,1),(7,1)]
def root8Node38Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3),(6,3)]
  | 29 => some [(2,2),(4,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5),(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(8,1)]
  | 37 => some [(0,2),(6,5)]
  | 38 => some [(0,4),(1,1)]
  | 39 => some [(0,1),(1,4),(3,4)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(0,5),(6,3)]
  | 42 => some [(2,2),(2,4)]
  | 43 => some [(1,3),(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(3,0),(5,0),(7,0)]
  | 49 => some [(2,3),(2,5),(4,5)]
  | 50 => some [(0,2),(1,0),(6,0)]
  | 51 => some [(0,2),(6,0)]
  | 52 => some [(1,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0),(7,4)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(5,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1),(8,1)]
  | 80 => some [(0,1),(6,5)]
  | 81 => some [(0,4),(6,2)]
  | 82 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => some [(0,0),(0,5),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 89 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => some [(0,3),(1,1),(6,1),(7,1)]
theorem root8Node38Domains1_fast_eq : root8Node38Domains1 = expandDomains root8Node38Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node38Domains1 v = expandDomains root8Node38Domains1Fast v from by decide) v
theorem root8Node38Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq (by decide)
theorem root8Node38Step1Narrowing_checked :
    checkNarrowing table36 root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root8Node38Domains0 root8Node38Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node38Step1Chunk0_0_checked, root8Node38Step1Chunk0_1_checked, root8Node38Step1Chunk0_2_checked, root8Node38Step1Chunk0_3_checked, root8Node38Step1Chunk0_4_checked, root8Node38Step1Chunk0_5_checked, root8Node38Step1Chunk1_0_checked, root8Node38Step1Chunk1_1_checked, root8Node38Step1Chunk1_2_checked, root8Node38Step1Chunk1_3_checked, root8Node38Step1Chunk1_4_checked, root8Node38Step1Chunk1_5_checked, root8Node38Step1Chunk2_0_checked, root8Node38Step1Chunk2_1_checked, root8Node38Step1Chunk2_2_checked, root8Node38Step1Chunk2_3_checked, root8Node38Step1Chunk2_4_checked, root8Node38Step1Chunk2_5_checked, root8Node38Step1Chunk3_0_checked, root8Node38Step1Chunk3_1_checked, root8Node38Step1Chunk3_2_checked, root8Node38Step1Chunk3_3_checked, root8Node38Step1Chunk3_4_checked, root8Node38Step1Chunk3_5_checked, root8Node38Step1Chunk4_0_checked, root8Node38Step1Chunk4_1_checked, root8Node38Step1Chunk4_2_checked, root8Node38Step1Chunk4_3_checked, root8Node38Step1Chunk4_4_checked, root8Node38Step1Chunk4_5_checked, root8Node38Step1Chunk5_0_checked, root8Node38Step1Chunk5_1_checked, root8Node38Step1Chunk5_2_checked, root8Node38Step1Chunk5_3_checked, root8Node38Step1Chunk5_4_checked, root8Node38Step1Chunk5_5_checked, root8Node38Step1Chunk6_0_checked, root8Node38Step1Chunk6_1_checked, root8Node38Step1Chunk6_2_checked, root8Node38Step1Chunk6_3_checked, root8Node38Step1Chunk6_4_checked, root8Node38Step1Chunk6_5_checked, root8Node38Step1Chunk7_0_checked, root8Node38Step1Chunk7_1_checked, root8Node38Step1Chunk7_2_checked, root8Node38Step1Chunk7_3_checked, root8Node38Step1Chunk7_4_checked, root8Node38Step1Chunk7_5_checked, root8Node38Step1Chunk8_0_checked, root8Node38Step1Chunk8_1_checked, root8Node38Step1Chunk8_2_checked, root8Node38Step1Chunk8_3_checked, root8Node38Step1Chunk8_4_checked, root8Node38Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node38Step1_checked :
    checkReplacement table36 root8Node38Domains0 root8Node38Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node38Domains0 root8Node38Domains1
    root8Node38Domains0Fast root8Node38Domains1Fast
    root8Node38Domains0_fast_eq root8Node38Domains1_fast_eq
    root8Node38Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
