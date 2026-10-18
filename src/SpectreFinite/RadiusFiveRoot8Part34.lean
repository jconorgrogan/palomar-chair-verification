module

public import SpectreFinite.RadiusFiveRoot8Part33
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable27
public import SpectreFinite.RadiusFiveTable4
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node87Domains2 (v : Fin 91) : List State :=
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
  | 12 => [(4,1),(5,1),(8,1)]
  | 13 => [(6,4)]
  | 14 => [(1,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(7,5)]
  | 22 => [(0,3)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(4,4),(8,4)]
  | 30 => [(7,3)]
  | 31 => [(4,2)]
  | 32 => [(5,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(7,1),(8,1)]
  | 39 => [(0,1),(1,5),(6,5)]
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(1,3),(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(5,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1),(8,1)]
  | 68 => [(0,2),(1,5),(6,5)]
  | 69 => [(0,4),(1,1),(6,1)]
  | 70 => [(0,5),(6,3)]
  | 71 => [(4,4),(7,2)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(1,3),(6,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(7,0),(8,0)]
  | 78 => [(1,1),(7,1)]
  | 79 => [(4,1),(7,5),(8,1)]
  | 80 => [(0,2),(6,0),(6,5)]
  | 81 => [(0,4),(1,1),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(6,5)]
  | 83 => [(0,4),(0,5),(6,2),(6,3)]
  | 84 => [(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,2)]
  | 87 => [(3,0),(5,0),(7,0)]
  | 88 => [(2,3),(2,5),(4,5)]
  | 89 => [(0,2),(1,0),(6,0),(7,0)]
  | _ => [(1,1),(4,3),(7,1)]
def root8Node87Domains2Fast (v : Fin 91) : Option (List State) :=
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
  | 12 => some [(4,1),(5,1),(8,1)]
  | 13 => some [(6,4)]
  | 14 => some [(1,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(7,5)]
  | 22 => some [(0,3)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(8,4)]
  | 30 => some [(7,3)]
  | 31 => some [(4,2)]
  | 32 => some [(5,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(5,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2)]
  | 87 => some [(3,0),(5,0),(7,0)]
  | 88 => some [(2,3),(2,5),(4,5)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node87Domains2_fast_eq : root8Node87Domains2 = expandDomains root8Node87Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node87Domains2 v = expandDomains root8Node87Domains2Fast v from by decide) v
theorem root8Node87Step2Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq (by decide)
theorem root8Node87Step2Narrowing_checked :
    checkNarrowing table54 root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node87Domains1 root8Node87Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node87Step2Chunk0_0_checked, root8Node87Step2Chunk0_1_checked, root8Node87Step2Chunk0_2_checked, root8Node87Step2Chunk0_3_checked, root8Node87Step2Chunk0_4_checked, root8Node87Step2Chunk0_5_checked, root8Node87Step2Chunk1_0_checked, root8Node87Step2Chunk1_1_checked, root8Node87Step2Chunk1_2_checked, root8Node87Step2Chunk1_3_checked, root8Node87Step2Chunk1_4_checked, root8Node87Step2Chunk1_5_checked, root8Node87Step2Chunk2_0_checked, root8Node87Step2Chunk2_1_checked, root8Node87Step2Chunk2_2_checked, root8Node87Step2Chunk2_3_checked, root8Node87Step2Chunk2_4_checked, root8Node87Step2Chunk2_5_checked, root8Node87Step2Chunk3_0_checked, root8Node87Step2Chunk3_1_checked, root8Node87Step2Chunk3_2_checked, root8Node87Step2Chunk3_3_checked, root8Node87Step2Chunk3_4_checked, root8Node87Step2Chunk3_5_checked, root8Node87Step2Chunk4_0_checked, root8Node87Step2Chunk4_1_checked, root8Node87Step2Chunk4_2_checked, root8Node87Step2Chunk4_3_checked, root8Node87Step2Chunk4_4_checked, root8Node87Step2Chunk4_5_checked, root8Node87Step2Chunk5_0_checked, root8Node87Step2Chunk5_1_checked, root8Node87Step2Chunk5_2_checked, root8Node87Step2Chunk5_3_checked, root8Node87Step2Chunk5_4_checked, root8Node87Step2Chunk5_5_checked, root8Node87Step2Chunk6_0_checked, root8Node87Step2Chunk6_1_checked, root8Node87Step2Chunk6_2_checked, root8Node87Step2Chunk6_3_checked, root8Node87Step2Chunk6_4_checked, root8Node87Step2Chunk6_5_checked, root8Node87Step2Chunk7_0_checked, root8Node87Step2Chunk7_1_checked, root8Node87Step2Chunk7_2_checked, root8Node87Step2Chunk7_3_checked, root8Node87Step2Chunk7_4_checked, root8Node87Step2Chunk7_5_checked, root8Node87Step2Chunk8_0_checked, root8Node87Step2Chunk8_1_checked, root8Node87Step2Chunk8_2_checked, root8Node87Step2Chunk8_3_checked, root8Node87Step2Chunk8_4_checked, root8Node87Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node87Step2_checked :
    checkReplacement table54 root8Node87Domains1 root8Node87Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node87Domains1 root8Node87Domains2
    root8Node87Domains1Fast root8Node87Domains2Fast
    root8Node87Domains1_fast_eq root8Node87Domains2_fast_eq
    root8Node87Step2Narrowing_checked (by decide)
def root8Node87Domains3 (v : Fin 91) : List State :=
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
  | 12 => [(4,1),(5,1),(8,1)]
  | 13 => [(6,4)]
  | 14 => [(1,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(7,5)]
  | 22 => [(0,3)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(4,4),(8,4)]
  | 30 => [(7,3)]
  | 31 => [(4,2)]
  | 32 => [(5,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(7,1),(8,1)]
  | 39 => [(1,5)]
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(6,3)]
  | 60 => [(7,2)]
  | 61 => [(5,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1),(8,1)]
  | 68 => [(0,2),(1,5)]
  | 69 => [(1,1),(6,1)]
  | 70 => [(0,5),(6,3)]
  | 71 => [(4,4),(7,2)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(1,3),(6,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(7,0),(8,0)]
  | 78 => [(1,1),(7,1)]
  | 79 => [(4,1),(7,5),(8,1)]
  | 80 => [(0,2),(6,0),(6,5)]
  | 81 => [(0,4),(1,1),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(6,5)]
  | 83 => [(0,4),(0,5),(6,2),(6,3)]
  | 84 => [(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,2)]
  | 87 => [(3,0),(5,0),(7,0)]
  | 88 => [(2,3),(2,5),(4,5)]
  | 89 => [(0,2),(1,0),(6,0),(7,0)]
  | _ => [(1,1),(4,3),(7,1)]
def root8Node87Domains3Fast (v : Fin 91) : Option (List State) :=
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
  | 12 => some [(4,1),(5,1),(8,1)]
  | 13 => some [(6,4)]
  | 14 => some [(1,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(7,5)]
  | 22 => some [(0,3)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(8,4)]
  | 30 => some [(7,3)]
  | 31 => some [(4,2)]
  | 32 => some [(5,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5)]
  | 69 => some [(1,1),(6,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2)]
  | 87 => some [(3,0),(5,0),(7,0)]
  | 88 => some [(2,3),(2,5),(4,5)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node87Domains3_fast_eq : root8Node87Domains3 = expandDomains root8Node87Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node87Domains3 v = expandDomains root8Node87Domains3Fast v from by decide) v
theorem root8Node87Step3Chunk0_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_0⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk0_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_1⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk0_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_2⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk0_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_3⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk0_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_4⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk0_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_5⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk1_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_0⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk1_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_1⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk1_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_2⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk1_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_3⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk1_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_4⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk1_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_5⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk2_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_0⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk2_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_1⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk2_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_2⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk2_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_3⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk2_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_4⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk2_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_5⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk3_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_0⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk3_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_1⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk3_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_2⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk3_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_3⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk3_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_4⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk3_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_5⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk4_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_0⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk4_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_1⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk4_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_2⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk4_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_3⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk4_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_4⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk4_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_5⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk5_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_0⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk5_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_1⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk5_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_2⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk5_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_3⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk5_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_4⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk5_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_5⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk6_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_0⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk6_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_1⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk6_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_2⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk6_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_3⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk6_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_4⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk6_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_5⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk7_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_0⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk7_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_1⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk7_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_2⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk7_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_3⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk7_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_4⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk7_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_5⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk8_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_0⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk8_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_1⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk8_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_2⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk8_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_3⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk8_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_4⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Chunk8_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_5⟩
      root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq (by decide)
theorem root8Node87Step3Narrowing_checked :
    checkNarrowing table27 root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkNarrowing_flatten table27Scope [table27Rows0_0,table27Rows0_1,table27Rows0_2,table27Rows0_3,table27Rows0_4,table27Rows0_5,table27Rows1_0,table27Rows1_1,table27Rows1_2,table27Rows1_3,table27Rows1_4,table27Rows1_5,table27Rows2_0,table27Rows2_1,table27Rows2_2,table27Rows2_3,table27Rows2_4,table27Rows2_5,table27Rows3_0,table27Rows3_1,table27Rows3_2,table27Rows3_3,table27Rows3_4,table27Rows3_5,table27Rows4_0,table27Rows4_1,table27Rows4_2,table27Rows4_3,table27Rows4_4,table27Rows4_5,table27Rows5_0,table27Rows5_1,table27Rows5_2,table27Rows5_3,table27Rows5_4,table27Rows5_5,table27Rows6_0,table27Rows6_1,table27Rows6_2,table27Rows6_3,table27Rows6_4,table27Rows6_5,table27Rows7_0,table27Rows7_1,table27Rows7_2,table27Rows7_3,table27Rows7_4,table27Rows7_5,table27Rows8_0,table27Rows8_1,table27Rows8_2,table27Rows8_3,table27Rows8_4,table27Rows8_5]
    root8Node87Domains2 root8Node87Domains3 (by
      simp only [List.all_cons, List.all_nil, root8Node87Step3Chunk0_0_checked, root8Node87Step3Chunk0_1_checked, root8Node87Step3Chunk0_2_checked, root8Node87Step3Chunk0_3_checked, root8Node87Step3Chunk0_4_checked, root8Node87Step3Chunk0_5_checked, root8Node87Step3Chunk1_0_checked, root8Node87Step3Chunk1_1_checked, root8Node87Step3Chunk1_2_checked, root8Node87Step3Chunk1_3_checked, root8Node87Step3Chunk1_4_checked, root8Node87Step3Chunk1_5_checked, root8Node87Step3Chunk2_0_checked, root8Node87Step3Chunk2_1_checked, root8Node87Step3Chunk2_2_checked, root8Node87Step3Chunk2_3_checked, root8Node87Step3Chunk2_4_checked, root8Node87Step3Chunk2_5_checked, root8Node87Step3Chunk3_0_checked, root8Node87Step3Chunk3_1_checked, root8Node87Step3Chunk3_2_checked, root8Node87Step3Chunk3_3_checked, root8Node87Step3Chunk3_4_checked, root8Node87Step3Chunk3_5_checked, root8Node87Step3Chunk4_0_checked, root8Node87Step3Chunk4_1_checked, root8Node87Step3Chunk4_2_checked, root8Node87Step3Chunk4_3_checked, root8Node87Step3Chunk4_4_checked, root8Node87Step3Chunk4_5_checked, root8Node87Step3Chunk5_0_checked, root8Node87Step3Chunk5_1_checked, root8Node87Step3Chunk5_2_checked, root8Node87Step3Chunk5_3_checked, root8Node87Step3Chunk5_4_checked, root8Node87Step3Chunk5_5_checked, root8Node87Step3Chunk6_0_checked, root8Node87Step3Chunk6_1_checked, root8Node87Step3Chunk6_2_checked, root8Node87Step3Chunk6_3_checked, root8Node87Step3Chunk6_4_checked, root8Node87Step3Chunk6_5_checked, root8Node87Step3Chunk7_0_checked, root8Node87Step3Chunk7_1_checked, root8Node87Step3Chunk7_2_checked, root8Node87Step3Chunk7_3_checked, root8Node87Step3Chunk7_4_checked, root8Node87Step3Chunk7_5_checked, root8Node87Step3Chunk8_0_checked, root8Node87Step3Chunk8_1_checked, root8Node87Step3Chunk8_2_checked, root8Node87Step3Chunk8_3_checked, root8Node87Step3Chunk8_4_checked, root8Node87Step3Chunk8_5_checked, Bool.true_and])
theorem root8Node87Step3_checked :
    checkReplacement table27 root8Node87Domains2 root8Node87Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root8Node87Domains2 root8Node87Domains3
    root8Node87Domains2Fast root8Node87Domains3Fast
    root8Node87Domains2_fast_eq root8Node87Domains3_fast_eq
    root8Node87Step3Narrowing_checked (by decide)
def root8Node88Domains0 : Domains 91 State := restrict root8Node87Domains3 19 (7,3)
def root8Node88Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 12 => some [(4,1),(5,1),(8,1)]
  | 13 => some [(6,4)]
  | 14 => some [(1,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(7,5)]
  | 22 => some [(0,3)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(8,4)]
  | 30 => some [(7,3)]
  | 31 => some [(4,2)]
  | 32 => some [(5,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5)]
  | 69 => some [(1,1),(6,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2)]
  | 87 => some [(3,0),(5,0),(7,0)]
  | 88 => some [(2,3),(2,5),(4,5)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node88Domains0_fast_eq : root8Node88Domains0 = expandDomains root8Node88Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node88Domains0 v = expandDomains root8Node88Domains0Fast v from by decide) v
def root8Node88Domains1 (v : Fin 91) : List State :=
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
  | 12 => [(4,1),(5,1),(8,1)]
  | 13 => [(6,4)]
  | 14 => [(1,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(7,5)]
  | 22 => [(0,3)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(4,4),(8,4)]
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
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(5,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5),(6,3)]
  | 71 => [(4,4),(7,2)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(6,3)]
  | 74 => [(2,2),(2,4)]
  | 75 => [(1,3),(3,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(1,1),(7,1)]
  | 79 => [(4,1),(7,5)]
  | 80 => [(0,2),(6,0)]
  | 81 => [(1,1),(7,1)]
  | 82 => [(0,1),(6,5)]
  | 83 => [(0,4),(6,2)]
  | 84 => [(5,4),(8,4)]
  | 85 => [(7,3),(8,3)]
  | 86 => [(5,2),(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0),(7,0)]
  | _ => [(4,3),(7,1)]
def root8Node88Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 12 => some [(4,1),(5,1),(8,1)]
  | 13 => some [(6,4)]
  | 14 => some [(1,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(7,5)]
  | 22 => some [(0,3)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,4),(8,4)]
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
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(6,3)]
  | 74 => some [(2,2),(2,4)]
  | 75 => some [(1,3),(3,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5)]
  | 80 => some [(0,2),(6,0)]
  | 81 => some [(1,1),(7,1)]
  | 82 => some [(0,1),(6,5)]
  | 83 => some [(0,4),(6,2)]
  | 84 => some [(5,4),(8,4)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0),(7,0)]
  | _ => some [(4,3),(7,1)]
theorem root8Node88Domains1_fast_eq : root8Node88Domains1 = expandDomains root8Node88Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node88Domains1 v = expandDomains root8Node88Domains1Fast v from by decide) v
theorem root8Node88Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq (by decide)
theorem root8Node88Step1Narrowing_checked :
    checkNarrowing table56 root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root8Node88Domains0 root8Node88Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node88Step1Chunk0_0_checked, root8Node88Step1Chunk0_1_checked, root8Node88Step1Chunk0_2_checked, root8Node88Step1Chunk0_3_checked, root8Node88Step1Chunk0_4_checked, root8Node88Step1Chunk0_5_checked, root8Node88Step1Chunk1_0_checked, root8Node88Step1Chunk1_1_checked, root8Node88Step1Chunk1_2_checked, root8Node88Step1Chunk1_3_checked, root8Node88Step1Chunk1_4_checked, root8Node88Step1Chunk1_5_checked, root8Node88Step1Chunk2_0_checked, root8Node88Step1Chunk2_1_checked, root8Node88Step1Chunk2_2_checked, root8Node88Step1Chunk2_3_checked, root8Node88Step1Chunk2_4_checked, root8Node88Step1Chunk2_5_checked, root8Node88Step1Chunk3_0_checked, root8Node88Step1Chunk3_1_checked, root8Node88Step1Chunk3_2_checked, root8Node88Step1Chunk3_3_checked, root8Node88Step1Chunk3_4_checked, root8Node88Step1Chunk3_5_checked, root8Node88Step1Chunk4_0_checked, root8Node88Step1Chunk4_1_checked, root8Node88Step1Chunk4_2_checked, root8Node88Step1Chunk4_3_checked, root8Node88Step1Chunk4_4_checked, root8Node88Step1Chunk4_5_checked, root8Node88Step1Chunk5_0_checked, root8Node88Step1Chunk5_1_checked, root8Node88Step1Chunk5_2_checked, root8Node88Step1Chunk5_3_checked, root8Node88Step1Chunk5_4_checked, root8Node88Step1Chunk5_5_checked, root8Node88Step1Chunk6_0_checked, root8Node88Step1Chunk6_1_checked, root8Node88Step1Chunk6_2_checked, root8Node88Step1Chunk6_3_checked, root8Node88Step1Chunk6_4_checked, root8Node88Step1Chunk6_5_checked, root8Node88Step1Chunk7_0_checked, root8Node88Step1Chunk7_1_checked, root8Node88Step1Chunk7_2_checked, root8Node88Step1Chunk7_3_checked, root8Node88Step1Chunk7_4_checked, root8Node88Step1Chunk7_5_checked, root8Node88Step1Chunk8_0_checked, root8Node88Step1Chunk8_1_checked, root8Node88Step1Chunk8_2_checked, root8Node88Step1Chunk8_3_checked, root8Node88Step1Chunk8_4_checked, root8Node88Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node88Step1_checked :
    checkReplacement table56 root8Node88Domains0 root8Node88Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node88Domains0 root8Node88Domains1
    root8Node88Domains0Fast root8Node88Domains1Fast
    root8Node88Domains0_fast_eq root8Node88Domains1_fast_eq
    root8Node88Step1Narrowing_checked (by decide)
def root8Node88Domains2 (v : Fin 91) : List State :=
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
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(5,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5),(6,3)]
  | 71 => [(4,4),(7,2)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(6,3)]
  | 74 => [(2,2),(2,4)]
  | 75 => [(1,3),(3,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(1,1),(7,1)]
  | 79 => [(4,1),(7,5)]
  | 80 => [(0,2),(6,0)]
  | 81 => [(1,1),(7,1)]
  | 82 => [(0,1),(6,5)]
  | 83 => [(0,4),(6,2)]
  | 84 => [(5,4),(8,4)]
  | 85 => [(7,3),(8,3)]
  | 86 => [(5,2),(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0),(7,0)]
  | _ => [(4,3),(7,1)]
def root8Node88Domains2Fast (v : Fin 91) : Option (List State) :=
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
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(6,3)]
  | 74 => some [(2,2),(2,4)]
  | 75 => some [(1,3),(3,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5)]
  | 80 => some [(0,2),(6,0)]
  | 81 => some [(1,1),(7,1)]
  | 82 => some [(0,1),(6,5)]
  | 83 => some [(0,4),(6,2)]
  | 84 => some [(5,4),(8,4)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0),(7,0)]
  | _ => some [(4,3),(7,1)]
theorem root8Node88Domains2_fast_eq : root8Node88Domains2 = expandDomains root8Node88Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node88Domains2 v = expandDomains root8Node88Domains2Fast v from by decide) v
theorem root8Node88Step2Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq (by decide)
theorem root8Node88Step2Narrowing_checked :
    checkNarrowing table4 root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkNarrowing_flatten table4Scope [table4Rows0_0,table4Rows0_1,table4Rows0_2,table4Rows0_3,table4Rows0_4,table4Rows0_5,table4Rows1_0,table4Rows1_1,table4Rows1_2,table4Rows1_3,table4Rows1_4,table4Rows1_5,table4Rows2_0,table4Rows2_1,table4Rows2_2,table4Rows2_3,table4Rows2_4,table4Rows2_5,table4Rows3_0,table4Rows3_1,table4Rows3_2,table4Rows3_3,table4Rows3_4,table4Rows3_5,table4Rows4_0,table4Rows4_1,table4Rows4_2,table4Rows4_3,table4Rows4_4,table4Rows4_5,table4Rows5_0,table4Rows5_1,table4Rows5_2,table4Rows5_3,table4Rows5_4,table4Rows5_5,table4Rows6_0,table4Rows6_1,table4Rows6_2,table4Rows6_3,table4Rows6_4,table4Rows6_5,table4Rows7_0,table4Rows7_1,table4Rows7_2,table4Rows7_3,table4Rows7_4,table4Rows7_5,table4Rows8_0,table4Rows8_1,table4Rows8_2,table4Rows8_3,table4Rows8_4,table4Rows8_5]
    root8Node88Domains1 root8Node88Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node88Step2Chunk0_0_checked, root8Node88Step2Chunk0_1_checked, root8Node88Step2Chunk0_2_checked, root8Node88Step2Chunk0_3_checked, root8Node88Step2Chunk0_4_checked, root8Node88Step2Chunk0_5_checked, root8Node88Step2Chunk1_0_checked, root8Node88Step2Chunk1_1_checked, root8Node88Step2Chunk1_2_checked, root8Node88Step2Chunk1_3_checked, root8Node88Step2Chunk1_4_checked, root8Node88Step2Chunk1_5_checked, root8Node88Step2Chunk2_0_checked, root8Node88Step2Chunk2_1_checked, root8Node88Step2Chunk2_2_checked, root8Node88Step2Chunk2_3_checked, root8Node88Step2Chunk2_4_checked, root8Node88Step2Chunk2_5_checked, root8Node88Step2Chunk3_0_checked, root8Node88Step2Chunk3_1_checked, root8Node88Step2Chunk3_2_checked, root8Node88Step2Chunk3_3_checked, root8Node88Step2Chunk3_4_checked, root8Node88Step2Chunk3_5_checked, root8Node88Step2Chunk4_0_checked, root8Node88Step2Chunk4_1_checked, root8Node88Step2Chunk4_2_checked, root8Node88Step2Chunk4_3_checked, root8Node88Step2Chunk4_4_checked, root8Node88Step2Chunk4_5_checked, root8Node88Step2Chunk5_0_checked, root8Node88Step2Chunk5_1_checked, root8Node88Step2Chunk5_2_checked, root8Node88Step2Chunk5_3_checked, root8Node88Step2Chunk5_4_checked, root8Node88Step2Chunk5_5_checked, root8Node88Step2Chunk6_0_checked, root8Node88Step2Chunk6_1_checked, root8Node88Step2Chunk6_2_checked, root8Node88Step2Chunk6_3_checked, root8Node88Step2Chunk6_4_checked, root8Node88Step2Chunk6_5_checked, root8Node88Step2Chunk7_0_checked, root8Node88Step2Chunk7_1_checked, root8Node88Step2Chunk7_2_checked, root8Node88Step2Chunk7_3_checked, root8Node88Step2Chunk7_4_checked, root8Node88Step2Chunk7_5_checked, root8Node88Step2Chunk8_0_checked, root8Node88Step2Chunk8_1_checked, root8Node88Step2Chunk8_2_checked, root8Node88Step2Chunk8_3_checked, root8Node88Step2Chunk8_4_checked, root8Node88Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node88Step2_checked :
    checkReplacement table4 root8Node88Domains1 root8Node88Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node88Domains1 root8Node88Domains2
    root8Node88Domains1Fast root8Node88Domains2Fast
    root8Node88Domains1_fast_eq root8Node88Domains2_fast_eq
    root8Node88Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
