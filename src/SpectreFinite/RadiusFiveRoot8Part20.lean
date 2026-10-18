module

public import SpectreFinite.RadiusFiveRoot8Part19
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node48Domains2 (v : Fin 91) : List State :=
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
  | 28 => [(6,3)]
  | 29 => [(2,2)]
  | 30 => [(4,3)]
  | 31 => [(3,5),(7,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(0,1)]
  | 40 => [(1,4),(7,4)]
  | 41 => [(0,5),(6,3)]
  | 42 => [(2,2),(2,4)]
  | 43 => [(1,3),(3,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(0,2),(6,0)]
  | 52 => [(1,1),(7,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0),(7,4)]
  | 73 => [(1,3),(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(7,0)]
  | 78 => [(6,1)]
  | 79 => [(5,1),(8,1)]
  | 80 => [(0,1),(6,5)]
  | 81 => [(0,4),(6,2)]
  | 82 => [(1,4),(3,4),(7,4)]
  | 83 => [(0,5),(6,3)]
  | 84 => [(4,4),(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(1,0),(3,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5)]
  | 89 => [(0,2),(6,0)]
  | _ => [(1,1),(7,1)]
def root8Node48Domains2Fast (v : Fin 91) : Option (List State) :=
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
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5),(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(0,5),(6,3)]
  | 42 => some [(2,2),(2,4)]
  | 43 => some [(1,3),(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,2),(6,0)]
  | 52 => some [(1,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0),(7,4)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1),(8,1)]
  | 80 => some [(0,1),(6,5)]
  | 81 => some [(0,4),(6,2)]
  | 82 => some [(1,4),(3,4),(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node48Domains2_fast_eq : root8Node48Domains2 = expandDomains root8Node48Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node48Domains2 v = expandDomains root8Node48Domains2Fast v from by decide) v
theorem root8Node48Step2Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq (by decide)
theorem root8Node48Step2Narrowing_checked :
    checkNarrowing table52 root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root8Node48Domains1 root8Node48Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node48Step2Chunk0_0_checked, root8Node48Step2Chunk0_1_checked, root8Node48Step2Chunk0_2_checked, root8Node48Step2Chunk0_3_checked, root8Node48Step2Chunk0_4_checked, root8Node48Step2Chunk0_5_checked, root8Node48Step2Chunk1_0_checked, root8Node48Step2Chunk1_1_checked, root8Node48Step2Chunk1_2_checked, root8Node48Step2Chunk1_3_checked, root8Node48Step2Chunk1_4_checked, root8Node48Step2Chunk1_5_checked, root8Node48Step2Chunk2_0_checked, root8Node48Step2Chunk2_1_checked, root8Node48Step2Chunk2_2_checked, root8Node48Step2Chunk2_3_checked, root8Node48Step2Chunk2_4_checked, root8Node48Step2Chunk2_5_checked, root8Node48Step2Chunk3_0_checked, root8Node48Step2Chunk3_1_checked, root8Node48Step2Chunk3_2_checked, root8Node48Step2Chunk3_3_checked, root8Node48Step2Chunk3_4_checked, root8Node48Step2Chunk3_5_checked, root8Node48Step2Chunk4_0_checked, root8Node48Step2Chunk4_1_checked, root8Node48Step2Chunk4_2_checked, root8Node48Step2Chunk4_3_checked, root8Node48Step2Chunk4_4_checked, root8Node48Step2Chunk4_5_checked, root8Node48Step2Chunk5_0_checked, root8Node48Step2Chunk5_1_checked, root8Node48Step2Chunk5_2_checked, root8Node48Step2Chunk5_3_checked, root8Node48Step2Chunk5_4_checked, root8Node48Step2Chunk5_5_checked, root8Node48Step2Chunk6_0_checked, root8Node48Step2Chunk6_1_checked, root8Node48Step2Chunk6_2_checked, root8Node48Step2Chunk6_3_checked, root8Node48Step2Chunk6_4_checked, root8Node48Step2Chunk6_5_checked, root8Node48Step2Chunk7_0_checked, root8Node48Step2Chunk7_1_checked, root8Node48Step2Chunk7_2_checked, root8Node48Step2Chunk7_3_checked, root8Node48Step2Chunk7_4_checked, root8Node48Step2Chunk7_5_checked, root8Node48Step2Chunk8_0_checked, root8Node48Step2Chunk8_1_checked, root8Node48Step2Chunk8_2_checked, root8Node48Step2Chunk8_3_checked, root8Node48Step2Chunk8_4_checked, root8Node48Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node48Step2_checked :
    checkReplacement table52 root8Node48Domains1 root8Node48Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node48Domains1 root8Node48Domains2
    root8Node48Domains1Fast root8Node48Domains2Fast
    root8Node48Domains1_fast_eq root8Node48Domains2_fast_eq
    root8Node48Step2Narrowing_checked (by decide)
def root8Node49Domains0 : Domains 91 State := restrict root8Node48Domains2 31 (3,5)
def root8Node49Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(0,5),(6,3)]
  | 42 => some [(2,2),(2,4)]
  | 43 => some [(1,3),(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,2),(6,0)]
  | 52 => some [(1,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0),(7,4)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1),(8,1)]
  | 80 => some [(0,1),(6,5)]
  | 81 => some [(0,4),(6,2)]
  | 82 => some [(1,4),(3,4),(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node49Domains0_fast_eq : root8Node49Domains0 = expandDomains root8Node49Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node49Domains0 v = expandDomains root8Node49Domains0Fast v from by decide) v
def root8Node49Domains1 (v : Fin 91) : List State :=
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
  | 28 => [(6,3)]
  | 29 => [(2,2)]
  | 30 => [(4,3)]
  | 31 => [(3,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(0,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(2,4)]
  | 43 => [(1,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(7,0)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(1,4),(3,4)]
  | 83 => [(0,5),(6,3)]
  | 84 => [(4,4),(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(3,0),(7,0)]
  | 88 => [(2,3),(2,5)]
  | 89 => [(0,2),(6,0)]
  | _ => [(1,1),(7,1)]
def root8Node49Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,4)]
  | 43 => some [(1,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(1,4),(3,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(3,0),(7,0)]
  | 88 => some [(2,3),(2,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node49Domains1_fast_eq : root8Node49Domains1 = expandDomains root8Node49Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node49Domains1 v = expandDomains root8Node49Domains1Fast v from by decide) v
theorem root8Node49Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq (by decide)
theorem root8Node49Step1Narrowing_checked :
    checkNarrowing table54 root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node49Domains0 root8Node49Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node49Step1Chunk0_0_checked, root8Node49Step1Chunk0_1_checked, root8Node49Step1Chunk0_2_checked, root8Node49Step1Chunk0_3_checked, root8Node49Step1Chunk0_4_checked, root8Node49Step1Chunk0_5_checked, root8Node49Step1Chunk1_0_checked, root8Node49Step1Chunk1_1_checked, root8Node49Step1Chunk1_2_checked, root8Node49Step1Chunk1_3_checked, root8Node49Step1Chunk1_4_checked, root8Node49Step1Chunk1_5_checked, root8Node49Step1Chunk2_0_checked, root8Node49Step1Chunk2_1_checked, root8Node49Step1Chunk2_2_checked, root8Node49Step1Chunk2_3_checked, root8Node49Step1Chunk2_4_checked, root8Node49Step1Chunk2_5_checked, root8Node49Step1Chunk3_0_checked, root8Node49Step1Chunk3_1_checked, root8Node49Step1Chunk3_2_checked, root8Node49Step1Chunk3_3_checked, root8Node49Step1Chunk3_4_checked, root8Node49Step1Chunk3_5_checked, root8Node49Step1Chunk4_0_checked, root8Node49Step1Chunk4_1_checked, root8Node49Step1Chunk4_2_checked, root8Node49Step1Chunk4_3_checked, root8Node49Step1Chunk4_4_checked, root8Node49Step1Chunk4_5_checked, root8Node49Step1Chunk5_0_checked, root8Node49Step1Chunk5_1_checked, root8Node49Step1Chunk5_2_checked, root8Node49Step1Chunk5_3_checked, root8Node49Step1Chunk5_4_checked, root8Node49Step1Chunk5_5_checked, root8Node49Step1Chunk6_0_checked, root8Node49Step1Chunk6_1_checked, root8Node49Step1Chunk6_2_checked, root8Node49Step1Chunk6_3_checked, root8Node49Step1Chunk6_4_checked, root8Node49Step1Chunk6_5_checked, root8Node49Step1Chunk7_0_checked, root8Node49Step1Chunk7_1_checked, root8Node49Step1Chunk7_2_checked, root8Node49Step1Chunk7_3_checked, root8Node49Step1Chunk7_4_checked, root8Node49Step1Chunk7_5_checked, root8Node49Step1Chunk8_0_checked, root8Node49Step1Chunk8_1_checked, root8Node49Step1Chunk8_2_checked, root8Node49Step1Chunk8_3_checked, root8Node49Step1Chunk8_4_checked, root8Node49Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node49Step1_checked :
    checkReplacement table54 root8Node49Domains0 root8Node49Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node49Domains0 root8Node49Domains1
    root8Node49Domains0Fast root8Node49Domains1Fast
    root8Node49Domains0_fast_eq root8Node49Domains1_fast_eq
    root8Node49Step1Narrowing_checked (by decide)
def root8Node50Domains0 : Domains 91 State := restrict root8Node49Domains1 76 (5,5)
def root8Node50Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,4)]
  | 43 => some [(1,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(1,4),(3,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(3,0),(7,0)]
  | 88 => some [(2,3),(2,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node50Domains0_fast_eq : root8Node50Domains0 = expandDomains root8Node50Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node50Domains0 v = expandDomains root8Node50Domains0Fast v from by decide) v
def root8Node50Domains1 (v : Fin 91) : List State :=
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
  | 28 => [(6,3)]
  | 29 => [(2,2)]
  | 30 => [(4,3)]
  | 31 => [(3,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(0,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(2,4)]
  | 43 => [(1,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(5,5)]
  | 77 => [(7,0)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(1,4)]
  | 83 => [(0,5)]
  | 84 => [(4,4)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(3,0)]
  | 88 => [(2,5)]
  | 89 => [(6,0)]
  | _ => [(7,1)]
def root8Node50Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,4)]
  | 43 => some [(1,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(1,4)]
  | 83 => some [(0,5)]
  | 84 => some [(4,4)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(3,0)]
  | 88 => some [(2,5)]
  | 89 => some [(6,0)]
  | _ => some [(7,1)]
theorem root8Node50Domains1_fast_eq : root8Node50Domains1 = expandDomains root8Node50Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node50Domains1 v = expandDomains root8Node50Domains1Fast v from by decide) v
theorem root8Node50Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq (by decide)
theorem root8Node50Step1Narrowing_checked :
    checkNarrowing table56 root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root8Node50Domains0 root8Node50Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node50Step1Chunk0_0_checked, root8Node50Step1Chunk0_1_checked, root8Node50Step1Chunk0_2_checked, root8Node50Step1Chunk0_3_checked, root8Node50Step1Chunk0_4_checked, root8Node50Step1Chunk0_5_checked, root8Node50Step1Chunk1_0_checked, root8Node50Step1Chunk1_1_checked, root8Node50Step1Chunk1_2_checked, root8Node50Step1Chunk1_3_checked, root8Node50Step1Chunk1_4_checked, root8Node50Step1Chunk1_5_checked, root8Node50Step1Chunk2_0_checked, root8Node50Step1Chunk2_1_checked, root8Node50Step1Chunk2_2_checked, root8Node50Step1Chunk2_3_checked, root8Node50Step1Chunk2_4_checked, root8Node50Step1Chunk2_5_checked, root8Node50Step1Chunk3_0_checked, root8Node50Step1Chunk3_1_checked, root8Node50Step1Chunk3_2_checked, root8Node50Step1Chunk3_3_checked, root8Node50Step1Chunk3_4_checked, root8Node50Step1Chunk3_5_checked, root8Node50Step1Chunk4_0_checked, root8Node50Step1Chunk4_1_checked, root8Node50Step1Chunk4_2_checked, root8Node50Step1Chunk4_3_checked, root8Node50Step1Chunk4_4_checked, root8Node50Step1Chunk4_5_checked, root8Node50Step1Chunk5_0_checked, root8Node50Step1Chunk5_1_checked, root8Node50Step1Chunk5_2_checked, root8Node50Step1Chunk5_3_checked, root8Node50Step1Chunk5_4_checked, root8Node50Step1Chunk5_5_checked, root8Node50Step1Chunk6_0_checked, root8Node50Step1Chunk6_1_checked, root8Node50Step1Chunk6_2_checked, root8Node50Step1Chunk6_3_checked, root8Node50Step1Chunk6_4_checked, root8Node50Step1Chunk6_5_checked, root8Node50Step1Chunk7_0_checked, root8Node50Step1Chunk7_1_checked, root8Node50Step1Chunk7_2_checked, root8Node50Step1Chunk7_3_checked, root8Node50Step1Chunk7_4_checked, root8Node50Step1Chunk7_5_checked, root8Node50Step1Chunk8_0_checked, root8Node50Step1Chunk8_1_checked, root8Node50Step1Chunk8_2_checked, root8Node50Step1Chunk8_3_checked, root8Node50Step1Chunk8_4_checked, root8Node50Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node50Step1_checked :
    checkReplacement table56 root8Node50Domains0 root8Node50Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node50Domains0 root8Node50Domains1
    root8Node50Domains0Fast root8Node50Domains1Fast
    root8Node50Domains0_fast_eq root8Node50Domains1_fast_eq
    root8Node50Step1Narrowing_checked (by decide)
theorem root8Node50Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node50Domains1 (.output 23) = true := by decide
def root8Node51Domains0 : Domains 91 State := restrict root8Node49Domains1 76 (8,5)
def root8Node51Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,4)]
  | 43 => some [(1,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(1,4),(3,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(3,0),(7,0)]
  | 88 => some [(2,3),(2,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node51Domains0_fast_eq : root8Node51Domains0 = expandDomains root8Node51Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node51Domains0 v = expandDomains root8Node51Domains0Fast v from by decide) v
def root8Node51Domains1 (v : Fin 91) : List State :=
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
  | 28 => [(6,3)]
  | 29 => [(2,2)]
  | 30 => [(4,3)]
  | 31 => [(3,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(0,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(2,4)]
  | 43 => [(1,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(3,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(2,3)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node51Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,4)]
  | 43 => some [(1,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(3,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(2,3)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node51Domains1_fast_eq : root8Node51Domains1 = expandDomains root8Node51Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node51Domains1 v = expandDomains root8Node51Domains1Fast v from by decide) v
theorem root8Node51Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq (by decide)
theorem root8Node51Step1Narrowing_checked :
    checkNarrowing table56 root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root8Node51Domains0 root8Node51Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node51Step1Chunk0_0_checked, root8Node51Step1Chunk0_1_checked, root8Node51Step1Chunk0_2_checked, root8Node51Step1Chunk0_3_checked, root8Node51Step1Chunk0_4_checked, root8Node51Step1Chunk0_5_checked, root8Node51Step1Chunk1_0_checked, root8Node51Step1Chunk1_1_checked, root8Node51Step1Chunk1_2_checked, root8Node51Step1Chunk1_3_checked, root8Node51Step1Chunk1_4_checked, root8Node51Step1Chunk1_5_checked, root8Node51Step1Chunk2_0_checked, root8Node51Step1Chunk2_1_checked, root8Node51Step1Chunk2_2_checked, root8Node51Step1Chunk2_3_checked, root8Node51Step1Chunk2_4_checked, root8Node51Step1Chunk2_5_checked, root8Node51Step1Chunk3_0_checked, root8Node51Step1Chunk3_1_checked, root8Node51Step1Chunk3_2_checked, root8Node51Step1Chunk3_3_checked, root8Node51Step1Chunk3_4_checked, root8Node51Step1Chunk3_5_checked, root8Node51Step1Chunk4_0_checked, root8Node51Step1Chunk4_1_checked, root8Node51Step1Chunk4_2_checked, root8Node51Step1Chunk4_3_checked, root8Node51Step1Chunk4_4_checked, root8Node51Step1Chunk4_5_checked, root8Node51Step1Chunk5_0_checked, root8Node51Step1Chunk5_1_checked, root8Node51Step1Chunk5_2_checked, root8Node51Step1Chunk5_3_checked, root8Node51Step1Chunk5_4_checked, root8Node51Step1Chunk5_5_checked, root8Node51Step1Chunk6_0_checked, root8Node51Step1Chunk6_1_checked, root8Node51Step1Chunk6_2_checked, root8Node51Step1Chunk6_3_checked, root8Node51Step1Chunk6_4_checked, root8Node51Step1Chunk6_5_checked, root8Node51Step1Chunk7_0_checked, root8Node51Step1Chunk7_1_checked, root8Node51Step1Chunk7_2_checked, root8Node51Step1Chunk7_3_checked, root8Node51Step1Chunk7_4_checked, root8Node51Step1Chunk7_5_checked, root8Node51Step1Chunk8_0_checked, root8Node51Step1Chunk8_1_checked, root8Node51Step1Chunk8_2_checked, root8Node51Step1Chunk8_3_checked, root8Node51Step1Chunk8_4_checked, root8Node51Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node51Step1_checked :
    checkReplacement table56 root8Node51Domains0 root8Node51Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node51Domains0 root8Node51Domains1
    root8Node51Domains0Fast root8Node51Domains1Fast
    root8Node51Domains0_fast_eq root8Node51Domains1_fast_eq
    root8Node51Step1Narrowing_checked (by decide)
theorem root8Node51Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node51Domains1 (.output 24) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
