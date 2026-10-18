module

public import SpectreFinite.RadiusFiveRoot4Part24
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable55
public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveTable6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node62Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(5,1)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(2,2)]
  | 16 => [(3,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(4,1)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(7,3)]
  | 31 => [(5,2)]
  | 32 => [(5,0)]
  | 33 => [(4,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(1,5)]
  | 40 => [(0,1),(6,4)]
  | 41 => [(1,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,3)]
  | 62 => [(8,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(1,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(1,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root4Node62Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(5,1)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(4,1)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(5,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(1,5)]
  | 40 => some [(0,1),(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root4Node62Domains2_fast_eq : root4Node62Domains2 = expandDomains root4Node62Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node62Domains2 v = expandDomains root4Node62Domains2Fast v from by decide) v
theorem root4Node62Step2Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq (by decide)
theorem root4Node62Step2Narrowing_checked :
    checkNarrowing table55 root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root4Node62Domains1 root4Node62Domains2 (by
      simp only [List.all_cons, List.all_nil, root4Node62Step2Chunk0_0_checked, root4Node62Step2Chunk0_1_checked, root4Node62Step2Chunk0_2_checked, root4Node62Step2Chunk0_3_checked, root4Node62Step2Chunk0_4_checked, root4Node62Step2Chunk0_5_checked, root4Node62Step2Chunk1_0_checked, root4Node62Step2Chunk1_1_checked, root4Node62Step2Chunk1_2_checked, root4Node62Step2Chunk1_3_checked, root4Node62Step2Chunk1_4_checked, root4Node62Step2Chunk1_5_checked, root4Node62Step2Chunk2_0_checked, root4Node62Step2Chunk2_1_checked, root4Node62Step2Chunk2_2_checked, root4Node62Step2Chunk2_3_checked, root4Node62Step2Chunk2_4_checked, root4Node62Step2Chunk2_5_checked, root4Node62Step2Chunk3_0_checked, root4Node62Step2Chunk3_1_checked, root4Node62Step2Chunk3_2_checked, root4Node62Step2Chunk3_3_checked, root4Node62Step2Chunk3_4_checked, root4Node62Step2Chunk3_5_checked, root4Node62Step2Chunk4_0_checked, root4Node62Step2Chunk4_1_checked, root4Node62Step2Chunk4_2_checked, root4Node62Step2Chunk4_3_checked, root4Node62Step2Chunk4_4_checked, root4Node62Step2Chunk4_5_checked, root4Node62Step2Chunk5_0_checked, root4Node62Step2Chunk5_1_checked, root4Node62Step2Chunk5_2_checked, root4Node62Step2Chunk5_3_checked, root4Node62Step2Chunk5_4_checked, root4Node62Step2Chunk5_5_checked, root4Node62Step2Chunk6_0_checked, root4Node62Step2Chunk6_1_checked, root4Node62Step2Chunk6_2_checked, root4Node62Step2Chunk6_3_checked, root4Node62Step2Chunk6_4_checked, root4Node62Step2Chunk6_5_checked, root4Node62Step2Chunk7_0_checked, root4Node62Step2Chunk7_1_checked, root4Node62Step2Chunk7_2_checked, root4Node62Step2Chunk7_3_checked, root4Node62Step2Chunk7_4_checked, root4Node62Step2Chunk7_5_checked, root4Node62Step2Chunk8_0_checked, root4Node62Step2Chunk8_1_checked, root4Node62Step2Chunk8_2_checked, root4Node62Step2Chunk8_3_checked, root4Node62Step2Chunk8_4_checked, root4Node62Step2Chunk8_5_checked, Bool.true_and])
theorem root4Node62Step2_checked :
    checkReplacement table55 root4Node62Domains1 root4Node62Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root4Node62Domains1 root4Node62Domains2
    root4Node62Domains1Fast root4Node62Domains2Fast
    root4Node62Domains1_fast_eq root4Node62Domains2_fast_eq
    root4Node62Step2Narrowing_checked (by decide)
def root4Node62Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(5,1)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(2,2)]
  | 16 => [(3,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(4,1)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(7,3)]
  | 31 => [(5,2)]
  | 32 => [(5,0)]
  | 33 => [(4,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(1,5)]
  | 40 => [(0,1),(6,4)]
  | 41 => [(1,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,3)]
  | 62 => [(8,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(1,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root4Node62Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(5,1)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(4,1)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(5,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(1,5)]
  | 40 => some [(0,1),(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node62Domains3_fast_eq : root4Node62Domains3 = expandDomains root4Node62Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node62Domains3 v = expandDomains root4Node62Domains3Fast v from by decide) v
theorem root4Node62Step3Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq (by decide)
theorem root4Node62Step3Narrowing_checked :
    checkNarrowing table56 root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root4Node62Domains2 root4Node62Domains3 (by
      simp only [List.all_cons, List.all_nil, root4Node62Step3Chunk0_0_checked, root4Node62Step3Chunk0_1_checked, root4Node62Step3Chunk0_2_checked, root4Node62Step3Chunk0_3_checked, root4Node62Step3Chunk0_4_checked, root4Node62Step3Chunk0_5_checked, root4Node62Step3Chunk1_0_checked, root4Node62Step3Chunk1_1_checked, root4Node62Step3Chunk1_2_checked, root4Node62Step3Chunk1_3_checked, root4Node62Step3Chunk1_4_checked, root4Node62Step3Chunk1_5_checked, root4Node62Step3Chunk2_0_checked, root4Node62Step3Chunk2_1_checked, root4Node62Step3Chunk2_2_checked, root4Node62Step3Chunk2_3_checked, root4Node62Step3Chunk2_4_checked, root4Node62Step3Chunk2_5_checked, root4Node62Step3Chunk3_0_checked, root4Node62Step3Chunk3_1_checked, root4Node62Step3Chunk3_2_checked, root4Node62Step3Chunk3_3_checked, root4Node62Step3Chunk3_4_checked, root4Node62Step3Chunk3_5_checked, root4Node62Step3Chunk4_0_checked, root4Node62Step3Chunk4_1_checked, root4Node62Step3Chunk4_2_checked, root4Node62Step3Chunk4_3_checked, root4Node62Step3Chunk4_4_checked, root4Node62Step3Chunk4_5_checked, root4Node62Step3Chunk5_0_checked, root4Node62Step3Chunk5_1_checked, root4Node62Step3Chunk5_2_checked, root4Node62Step3Chunk5_3_checked, root4Node62Step3Chunk5_4_checked, root4Node62Step3Chunk5_5_checked, root4Node62Step3Chunk6_0_checked, root4Node62Step3Chunk6_1_checked, root4Node62Step3Chunk6_2_checked, root4Node62Step3Chunk6_3_checked, root4Node62Step3Chunk6_4_checked, root4Node62Step3Chunk6_5_checked, root4Node62Step3Chunk7_0_checked, root4Node62Step3Chunk7_1_checked, root4Node62Step3Chunk7_2_checked, root4Node62Step3Chunk7_3_checked, root4Node62Step3Chunk7_4_checked, root4Node62Step3Chunk7_5_checked, root4Node62Step3Chunk8_0_checked, root4Node62Step3Chunk8_1_checked, root4Node62Step3Chunk8_2_checked, root4Node62Step3Chunk8_3_checked, root4Node62Step3Chunk8_4_checked, root4Node62Step3Chunk8_5_checked, Bool.true_and])
theorem root4Node62Step3_checked :
    checkReplacement table56 root4Node62Domains2 root4Node62Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root4Node62Domains2 root4Node62Domains3
    root4Node62Domains2Fast root4Node62Domains3Fast
    root4Node62Domains2_fast_eq root4Node62Domains3_fast_eq
    root4Node62Step3Narrowing_checked (by decide)
def root4Node62Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(5,1)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(2,2)]
  | 16 => [(3,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(4,1)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(7,3)]
  | 31 => [(5,2)]
  | 32 => [(5,0)]
  | 33 => [(4,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(1,5)]
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(8,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,3)]
  | 62 => [(8,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(1,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root4Node62Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(5,1)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(4,1)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(5,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(1,5)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node62Domains4_fast_eq : root4Node62Domains4 = expandDomains root4Node62Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node62Domains4 v = expandDomains root4Node62Domains4Fast v from by decide) v
theorem root4Node62Step4Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq (by decide)
theorem root4Node62Step4Narrowing_checked :
    checkNarrowing table6 root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkNarrowing_flatten table6Scope [table6Rows0_0,table6Rows0_1,table6Rows0_2,table6Rows0_3,table6Rows0_4,table6Rows0_5,table6Rows1_0,table6Rows1_1,table6Rows1_2,table6Rows1_3,table6Rows1_4,table6Rows1_5,table6Rows2_0,table6Rows2_1,table6Rows2_2,table6Rows2_3,table6Rows2_4,table6Rows2_5,table6Rows3_0,table6Rows3_1,table6Rows3_2,table6Rows3_3,table6Rows3_4,table6Rows3_5,table6Rows4_0,table6Rows4_1,table6Rows4_2,table6Rows4_3,table6Rows4_4,table6Rows4_5,table6Rows5_0,table6Rows5_1,table6Rows5_2,table6Rows5_3,table6Rows5_4,table6Rows5_5,table6Rows6_0,table6Rows6_1,table6Rows6_2,table6Rows6_3,table6Rows6_4,table6Rows6_5,table6Rows7_0,table6Rows7_1,table6Rows7_2,table6Rows7_3,table6Rows7_4,table6Rows7_5,table6Rows8_0,table6Rows8_1,table6Rows8_2,table6Rows8_3,table6Rows8_4,table6Rows8_5]
    root4Node62Domains3 root4Node62Domains4 (by
      simp only [List.all_cons, List.all_nil, root4Node62Step4Chunk0_0_checked, root4Node62Step4Chunk0_1_checked, root4Node62Step4Chunk0_2_checked, root4Node62Step4Chunk0_3_checked, root4Node62Step4Chunk0_4_checked, root4Node62Step4Chunk0_5_checked, root4Node62Step4Chunk1_0_checked, root4Node62Step4Chunk1_1_checked, root4Node62Step4Chunk1_2_checked, root4Node62Step4Chunk1_3_checked, root4Node62Step4Chunk1_4_checked, root4Node62Step4Chunk1_5_checked, root4Node62Step4Chunk2_0_checked, root4Node62Step4Chunk2_1_checked, root4Node62Step4Chunk2_2_checked, root4Node62Step4Chunk2_3_checked, root4Node62Step4Chunk2_4_checked, root4Node62Step4Chunk2_5_checked, root4Node62Step4Chunk3_0_checked, root4Node62Step4Chunk3_1_checked, root4Node62Step4Chunk3_2_checked, root4Node62Step4Chunk3_3_checked, root4Node62Step4Chunk3_4_checked, root4Node62Step4Chunk3_5_checked, root4Node62Step4Chunk4_0_checked, root4Node62Step4Chunk4_1_checked, root4Node62Step4Chunk4_2_checked, root4Node62Step4Chunk4_3_checked, root4Node62Step4Chunk4_4_checked, root4Node62Step4Chunk4_5_checked, root4Node62Step4Chunk5_0_checked, root4Node62Step4Chunk5_1_checked, root4Node62Step4Chunk5_2_checked, root4Node62Step4Chunk5_3_checked, root4Node62Step4Chunk5_4_checked, root4Node62Step4Chunk5_5_checked, root4Node62Step4Chunk6_0_checked, root4Node62Step4Chunk6_1_checked, root4Node62Step4Chunk6_2_checked, root4Node62Step4Chunk6_3_checked, root4Node62Step4Chunk6_4_checked, root4Node62Step4Chunk6_5_checked, root4Node62Step4Chunk7_0_checked, root4Node62Step4Chunk7_1_checked, root4Node62Step4Chunk7_2_checked, root4Node62Step4Chunk7_3_checked, root4Node62Step4Chunk7_4_checked, root4Node62Step4Chunk7_5_checked, root4Node62Step4Chunk8_0_checked, root4Node62Step4Chunk8_1_checked, root4Node62Step4Chunk8_2_checked, root4Node62Step4Chunk8_3_checked, root4Node62Step4Chunk8_4_checked, root4Node62Step4Chunk8_5_checked, Bool.true_and])
theorem root4Node62Step4_checked :
    checkReplacement table6 root4Node62Domains3 root4Node62Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root4Node62Domains3 root4Node62Domains4
    root4Node62Domains3Fast root4Node62Domains4Fast
    root4Node62Domains3_fast_eq root4Node62Domains4_fast_eq
    root4Node62Step4Narrowing_checked (by decide)
theorem root4Node62Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node62Domains4 (.output 30) = true := by decide
def root4Node63Domains0 : Domains 91 State := restrict root4Node61Domains3 12 (8,1)
def root4Node63Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(4,1)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(7,3)]
  | 31 => some [(5,2)]
  | 32 => some [(5,0)]
  | 33 => some [(4,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(1,5),(7,5)]
  | 40 => some [(0,1),(6,4)]
  | 41 => some [(1,2),(6,2)]
  | 42 => some [(8,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0),(8,0)]
  | 49 => some [(4,5),(7,3)]
  | 50 => some [(4,2),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(5,0),(5,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0),(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(5,0),(8,0)]
  | 76 => some [(4,5),(7,3)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(1,1),(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,4)]
  | 84 => some [(1,2),(6,2),(7,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root4Node63Domains0_fast_eq : root4Node63Domains0 = expandDomains root4Node63Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node63Domains0 v = expandDomains root4Node63Domains0Fast v from by decide) v
end SpectreFinite.HexSearch.RadiusFive
