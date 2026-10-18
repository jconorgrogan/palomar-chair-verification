module

public import SpectreFinite.RadiusFiveRoot8Part25
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable13
public import SpectreFinite.RadiusFiveTable5
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node62Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(4,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
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
  | 30 => [(8,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5),(6,5)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(1,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,4)]
  | 75 => [(1,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root8Node62Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
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
  | 30 => some [(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5),(6,5)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,4)]
  | 75 => some [(1,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root8Node62Domains2_fast_eq : root8Node62Domains2 = expandDomains root8Node62Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node62Domains2 v = expandDomains root8Node62Domains2Fast v from by decide) v
theorem root8Node62Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq (by decide)
theorem root8Node62Step2Narrowing_checked :
    checkNarrowing table65 root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root8Node62Domains1 root8Node62Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node62Step2Chunk0_0_checked, root8Node62Step2Chunk0_1_checked, root8Node62Step2Chunk0_2_checked, root8Node62Step2Chunk0_3_checked, root8Node62Step2Chunk0_4_checked, root8Node62Step2Chunk0_5_checked, root8Node62Step2Chunk1_0_checked, root8Node62Step2Chunk1_1_checked, root8Node62Step2Chunk1_2_checked, root8Node62Step2Chunk1_3_checked, root8Node62Step2Chunk1_4_checked, root8Node62Step2Chunk1_5_checked, root8Node62Step2Chunk2_0_checked, root8Node62Step2Chunk2_1_checked, root8Node62Step2Chunk2_2_checked, root8Node62Step2Chunk2_3_checked, root8Node62Step2Chunk2_4_checked, root8Node62Step2Chunk2_5_checked, root8Node62Step2Chunk3_0_checked, root8Node62Step2Chunk3_1_checked, root8Node62Step2Chunk3_2_checked, root8Node62Step2Chunk3_3_checked, root8Node62Step2Chunk3_4_checked, root8Node62Step2Chunk3_5_checked, root8Node62Step2Chunk4_0_checked, root8Node62Step2Chunk4_1_checked, root8Node62Step2Chunk4_2_checked, root8Node62Step2Chunk4_3_checked, root8Node62Step2Chunk4_4_checked, root8Node62Step2Chunk4_5_checked, root8Node62Step2Chunk5_0_checked, root8Node62Step2Chunk5_1_checked, root8Node62Step2Chunk5_2_checked, root8Node62Step2Chunk5_3_checked, root8Node62Step2Chunk5_4_checked, root8Node62Step2Chunk5_5_checked, root8Node62Step2Chunk6_0_checked, root8Node62Step2Chunk6_1_checked, root8Node62Step2Chunk6_2_checked, root8Node62Step2Chunk6_3_checked, root8Node62Step2Chunk6_4_checked, root8Node62Step2Chunk6_5_checked, root8Node62Step2Chunk7_0_checked, root8Node62Step2Chunk7_1_checked, root8Node62Step2Chunk7_2_checked, root8Node62Step2Chunk7_3_checked, root8Node62Step2Chunk7_4_checked, root8Node62Step2Chunk7_5_checked, root8Node62Step2Chunk8_0_checked, root8Node62Step2Chunk8_1_checked, root8Node62Step2Chunk8_2_checked, root8Node62Step2Chunk8_3_checked, root8Node62Step2Chunk8_4_checked, root8Node62Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node62Step2_checked :
    checkReplacement table65 root8Node62Domains1 root8Node62Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node62Domains1 root8Node62Domains2
    root8Node62Domains1Fast root8Node62Domains2Fast
    root8Node62Domains1_fast_eq root8Node62Domains2_fast_eq
    root8Node62Step2Narrowing_checked (by decide)
def root8Node63Domains0 : Domains 91 State := restrict root8Node62Domains2 20 (4,2)
def root8Node63Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4),(8,4)]
  | 30 => some [(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5),(6,5)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,4)]
  | 75 => some [(1,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root8Node63Domains0_fast_eq : root8Node63Domains0 = expandDomains root8Node63Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node63Domains0 v = expandDomains root8Node63Domains0Fast v from by decide) v
def root8Node63Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(4,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(7,4)]
  | 30 => [(8,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(6,5)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(1,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,4)]
  | 75 => [(1,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root8Node63Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4)]
  | 30 => some [(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(6,5)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,4)]
  | 75 => some [(1,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root8Node63Domains1_fast_eq : root8Node63Domains1 = expandDomains root8Node63Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node63Domains1 v = expandDomains root8Node63Domains1Fast v from by decide) v
theorem root8Node63Step1Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Narrowing_checked :
    checkNarrowing table5 root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_flatten table5Scope [table5Rows0_0,table5Rows0_1,table5Rows0_2,table5Rows0_3,table5Rows0_4,table5Rows0_5,table5Rows1_0,table5Rows1_1,table5Rows1_2,table5Rows1_3,table5Rows1_4,table5Rows1_5,table5Rows2_0,table5Rows2_1,table5Rows2_2,table5Rows2_3,table5Rows2_4,table5Rows2_5,table5Rows3_0,table5Rows3_1,table5Rows3_2,table5Rows3_3,table5Rows3_4,table5Rows3_5,table5Rows4_0,table5Rows4_1,table5Rows4_2,table5Rows4_3,table5Rows4_4,table5Rows4_5,table5Rows5_0,table5Rows5_1,table5Rows5_2,table5Rows5_3,table5Rows5_4,table5Rows5_5,table5Rows6_0,table5Rows6_1,table5Rows6_2,table5Rows6_3,table5Rows6_4,table5Rows6_5,table5Rows7_0,table5Rows7_1,table5Rows7_2,table5Rows7_3,table5Rows7_4,table5Rows7_5,table5Rows8_0,table5Rows8_1,table5Rows8_2,table5Rows8_3,table5Rows8_4,table5Rows8_5]
    root8Node63Domains0 root8Node63Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node63Step1Chunk0_0_checked, root8Node63Step1Chunk0_1_checked, root8Node63Step1Chunk0_2_checked, root8Node63Step1Chunk0_3_checked, root8Node63Step1Chunk0_4_checked, root8Node63Step1Chunk0_5_checked, root8Node63Step1Chunk1_0_checked, root8Node63Step1Chunk1_1_checked, root8Node63Step1Chunk1_2_checked, root8Node63Step1Chunk1_3_checked, root8Node63Step1Chunk1_4_checked, root8Node63Step1Chunk1_5_checked, root8Node63Step1Chunk2_0_checked, root8Node63Step1Chunk2_1_checked, root8Node63Step1Chunk2_2_checked, root8Node63Step1Chunk2_3_checked, root8Node63Step1Chunk2_4_checked, root8Node63Step1Chunk2_5_checked, root8Node63Step1Chunk3_0_checked, root8Node63Step1Chunk3_1_checked, root8Node63Step1Chunk3_2_checked, root8Node63Step1Chunk3_3_checked, root8Node63Step1Chunk3_4_checked, root8Node63Step1Chunk3_5_checked, root8Node63Step1Chunk4_0_checked, root8Node63Step1Chunk4_1_checked, root8Node63Step1Chunk4_2_checked, root8Node63Step1Chunk4_3_checked, root8Node63Step1Chunk4_4_checked, root8Node63Step1Chunk4_5_checked, root8Node63Step1Chunk5_0_checked, root8Node63Step1Chunk5_1_checked, root8Node63Step1Chunk5_2_checked, root8Node63Step1Chunk5_3_checked, root8Node63Step1Chunk5_4_checked, root8Node63Step1Chunk5_5_checked, root8Node63Step1Chunk6_0_checked, root8Node63Step1Chunk6_1_checked, root8Node63Step1Chunk6_2_checked, root8Node63Step1Chunk6_3_checked, root8Node63Step1Chunk6_4_checked, root8Node63Step1Chunk6_5_checked, root8Node63Step1Chunk7_0_checked, root8Node63Step1Chunk7_1_checked, root8Node63Step1Chunk7_2_checked, root8Node63Step1Chunk7_3_checked, root8Node63Step1Chunk7_4_checked, root8Node63Step1Chunk7_5_checked, root8Node63Step1Chunk8_0_checked, root8Node63Step1Chunk8_1_checked, root8Node63Step1Chunk8_2_checked, root8Node63Step1Chunk8_3_checked, root8Node63Step1Chunk8_4_checked, root8Node63Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node63Step1_checked :
    checkReplacement table5 root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq
    root8Node63Step1Narrowing_checked (by decide)
theorem root8Node63Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node63Domains1 (.output 30) = true := by decide
def root8Node64Domains0 : Domains 91 State := restrict root8Node62Domains2 20 (8,2)
def root8Node64Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4),(8,4)]
  | 30 => some [(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5),(6,5)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,4)]
  | 75 => some [(1,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root8Node64Domains0_fast_eq : root8Node64Domains0 = expandDomains root8Node64Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node64Domains0 v = expandDomains root8Node64Domains0Fast v from by decide) v
def root8Node64Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(4,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(8,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(1,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,4)]
  | 75 => [(1,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root8Node64Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,4)]
  | 75 => some [(1,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root8Node64Domains1_fast_eq : root8Node64Domains1 = expandDomains root8Node64Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node64Domains1 v = expandDomains root8Node64Domains1Fast v from by decide) v
theorem root8Node64Step1Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Narrowing_checked :
    checkNarrowing table5 root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_flatten table5Scope [table5Rows0_0,table5Rows0_1,table5Rows0_2,table5Rows0_3,table5Rows0_4,table5Rows0_5,table5Rows1_0,table5Rows1_1,table5Rows1_2,table5Rows1_3,table5Rows1_4,table5Rows1_5,table5Rows2_0,table5Rows2_1,table5Rows2_2,table5Rows2_3,table5Rows2_4,table5Rows2_5,table5Rows3_0,table5Rows3_1,table5Rows3_2,table5Rows3_3,table5Rows3_4,table5Rows3_5,table5Rows4_0,table5Rows4_1,table5Rows4_2,table5Rows4_3,table5Rows4_4,table5Rows4_5,table5Rows5_0,table5Rows5_1,table5Rows5_2,table5Rows5_3,table5Rows5_4,table5Rows5_5,table5Rows6_0,table5Rows6_1,table5Rows6_2,table5Rows6_3,table5Rows6_4,table5Rows6_5,table5Rows7_0,table5Rows7_1,table5Rows7_2,table5Rows7_3,table5Rows7_4,table5Rows7_5,table5Rows8_0,table5Rows8_1,table5Rows8_2,table5Rows8_3,table5Rows8_4,table5Rows8_5]
    root8Node64Domains0 root8Node64Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node64Step1Chunk0_0_checked, root8Node64Step1Chunk0_1_checked, root8Node64Step1Chunk0_2_checked, root8Node64Step1Chunk0_3_checked, root8Node64Step1Chunk0_4_checked, root8Node64Step1Chunk0_5_checked, root8Node64Step1Chunk1_0_checked, root8Node64Step1Chunk1_1_checked, root8Node64Step1Chunk1_2_checked, root8Node64Step1Chunk1_3_checked, root8Node64Step1Chunk1_4_checked, root8Node64Step1Chunk1_5_checked, root8Node64Step1Chunk2_0_checked, root8Node64Step1Chunk2_1_checked, root8Node64Step1Chunk2_2_checked, root8Node64Step1Chunk2_3_checked, root8Node64Step1Chunk2_4_checked, root8Node64Step1Chunk2_5_checked, root8Node64Step1Chunk3_0_checked, root8Node64Step1Chunk3_1_checked, root8Node64Step1Chunk3_2_checked, root8Node64Step1Chunk3_3_checked, root8Node64Step1Chunk3_4_checked, root8Node64Step1Chunk3_5_checked, root8Node64Step1Chunk4_0_checked, root8Node64Step1Chunk4_1_checked, root8Node64Step1Chunk4_2_checked, root8Node64Step1Chunk4_3_checked, root8Node64Step1Chunk4_4_checked, root8Node64Step1Chunk4_5_checked, root8Node64Step1Chunk5_0_checked, root8Node64Step1Chunk5_1_checked, root8Node64Step1Chunk5_2_checked, root8Node64Step1Chunk5_3_checked, root8Node64Step1Chunk5_4_checked, root8Node64Step1Chunk5_5_checked, root8Node64Step1Chunk6_0_checked, root8Node64Step1Chunk6_1_checked, root8Node64Step1Chunk6_2_checked, root8Node64Step1Chunk6_3_checked, root8Node64Step1Chunk6_4_checked, root8Node64Step1Chunk6_5_checked, root8Node64Step1Chunk7_0_checked, root8Node64Step1Chunk7_1_checked, root8Node64Step1Chunk7_2_checked, root8Node64Step1Chunk7_3_checked, root8Node64Step1Chunk7_4_checked, root8Node64Step1Chunk7_5_checked, root8Node64Step1Chunk8_0_checked, root8Node64Step1Chunk8_1_checked, root8Node64Step1Chunk8_2_checked, root8Node64Step1Chunk8_3_checked, root8Node64Step1Chunk8_4_checked, root8Node64Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node64Step1_checked :
    checkReplacement table5 root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq
    root8Node64Step1Narrowing_checked (by decide)
theorem root8Node64Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node64Domains1 (.output 31) = true := by decide
def root8Node65Domains0 : Domains 91 State := restrict root8Node61Domains4 0 (1,4)
def root8Node65Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5),(6,2)]
  | 2 => some [(4,4),(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(2,5),(4,5)]
  | 7 => some [(1,0),(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
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
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
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
  | 85 => some [(7,3)]
  | 86 => some [(5,2),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0),(7,0)]
  | _ => some [(4,3),(7,1)]
theorem root8Node65Domains0_fast_eq : root8Node65Domains0 = expandDomains root8Node65Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node65Domains0 v = expandDomains root8Node65Domains0Fast v from by decide) v
def root8Node65Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(2,5)]
  | 7 => [(6,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
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
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5),(6,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
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
  | 85 => [(7,3)]
  | 86 => [(5,2),(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0),(7,0)]
  | _ => [(4,3),(7,1)]
def root8Node65Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(2,5)]
  | 7 => some [(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
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
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
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
  | 85 => some [(7,3)]
  | 86 => some [(5,2),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0),(7,0)]
  | _ => some [(4,3),(7,1)]
theorem root8Node65Domains1_fast_eq : root8Node65Domains1 = expandDomains root8Node65Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node65Domains1 v = expandDomains root8Node65Domains1Fast v from by decide) v
theorem root8Node65Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq (by decide)
theorem root8Node65Step1Narrowing_checked :
    checkNarrowing table13 root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkNarrowing_flatten table13Scope [table13Rows0_0,table13Rows0_1,table13Rows0_2,table13Rows0_3,table13Rows0_4,table13Rows0_5,table13Rows1_0,table13Rows1_1,table13Rows1_2,table13Rows1_3,table13Rows1_4,table13Rows1_5,table13Rows2_0,table13Rows2_1,table13Rows2_2,table13Rows2_3,table13Rows2_4,table13Rows2_5,table13Rows3_0,table13Rows3_1,table13Rows3_2,table13Rows3_3,table13Rows3_4,table13Rows3_5,table13Rows4_0,table13Rows4_1,table13Rows4_2,table13Rows4_3,table13Rows4_4,table13Rows4_5,table13Rows5_0,table13Rows5_1,table13Rows5_2,table13Rows5_3,table13Rows5_4,table13Rows5_5,table13Rows6_0,table13Rows6_1,table13Rows6_2,table13Rows6_3,table13Rows6_4,table13Rows6_5,table13Rows7_0,table13Rows7_1,table13Rows7_2,table13Rows7_3,table13Rows7_4,table13Rows7_5,table13Rows8_0,table13Rows8_1,table13Rows8_2,table13Rows8_3,table13Rows8_4,table13Rows8_5]
    root8Node65Domains0 root8Node65Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node65Step1Chunk0_0_checked, root8Node65Step1Chunk0_1_checked, root8Node65Step1Chunk0_2_checked, root8Node65Step1Chunk0_3_checked, root8Node65Step1Chunk0_4_checked, root8Node65Step1Chunk0_5_checked, root8Node65Step1Chunk1_0_checked, root8Node65Step1Chunk1_1_checked, root8Node65Step1Chunk1_2_checked, root8Node65Step1Chunk1_3_checked, root8Node65Step1Chunk1_4_checked, root8Node65Step1Chunk1_5_checked, root8Node65Step1Chunk2_0_checked, root8Node65Step1Chunk2_1_checked, root8Node65Step1Chunk2_2_checked, root8Node65Step1Chunk2_3_checked, root8Node65Step1Chunk2_4_checked, root8Node65Step1Chunk2_5_checked, root8Node65Step1Chunk3_0_checked, root8Node65Step1Chunk3_1_checked, root8Node65Step1Chunk3_2_checked, root8Node65Step1Chunk3_3_checked, root8Node65Step1Chunk3_4_checked, root8Node65Step1Chunk3_5_checked, root8Node65Step1Chunk4_0_checked, root8Node65Step1Chunk4_1_checked, root8Node65Step1Chunk4_2_checked, root8Node65Step1Chunk4_3_checked, root8Node65Step1Chunk4_4_checked, root8Node65Step1Chunk4_5_checked, root8Node65Step1Chunk5_0_checked, root8Node65Step1Chunk5_1_checked, root8Node65Step1Chunk5_2_checked, root8Node65Step1Chunk5_3_checked, root8Node65Step1Chunk5_4_checked, root8Node65Step1Chunk5_5_checked, root8Node65Step1Chunk6_0_checked, root8Node65Step1Chunk6_1_checked, root8Node65Step1Chunk6_2_checked, root8Node65Step1Chunk6_3_checked, root8Node65Step1Chunk6_4_checked, root8Node65Step1Chunk6_5_checked, root8Node65Step1Chunk7_0_checked, root8Node65Step1Chunk7_1_checked, root8Node65Step1Chunk7_2_checked, root8Node65Step1Chunk7_3_checked, root8Node65Step1Chunk7_4_checked, root8Node65Step1Chunk7_5_checked, root8Node65Step1Chunk8_0_checked, root8Node65Step1Chunk8_1_checked, root8Node65Step1Chunk8_2_checked, root8Node65Step1Chunk8_3_checked, root8Node65Step1Chunk8_4_checked, root8Node65Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node65Step1_checked :
    checkReplacement table13 root8Node65Domains0 root8Node65Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node65Domains0 root8Node65Domains1
    root8Node65Domains0Fast root8Node65Domains1Fast
    root8Node65Domains0_fast_eq root8Node65Domains1_fast_eq
    root8Node65Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
