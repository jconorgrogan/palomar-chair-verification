module

public import SpectreFinite.RadiusFiveRoot5Part25
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node62Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(1,4)]
  | 13 => [(3,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(3,0)]
  | 19 => [(2,5)]
  | 20 => [(6,0)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(0,0)]
  | 28 => [(7,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(1,0)]
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
def root5Node62Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(1,4)]
  | 13 => some [(3,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
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
theorem root5Node62Domains2_fast_eq : root5Node62Domains2 = expandDomains root5Node62Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node62Domains2 v = expandDomains root5Node62Domains2Fast v from by decide) v
theorem root5Node62Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq (by decide)
theorem root5Node62Step2Narrowing_checked :
    checkNarrowing table56 root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root5Node62Domains1 root5Node62Domains2 (by
      simp only [List.all_cons, List.all_nil, root5Node62Step2Chunk0_0_checked, root5Node62Step2Chunk0_1_checked, root5Node62Step2Chunk0_2_checked, root5Node62Step2Chunk0_3_checked, root5Node62Step2Chunk0_4_checked, root5Node62Step2Chunk0_5_checked, root5Node62Step2Chunk1_0_checked, root5Node62Step2Chunk1_1_checked, root5Node62Step2Chunk1_2_checked, root5Node62Step2Chunk1_3_checked, root5Node62Step2Chunk1_4_checked, root5Node62Step2Chunk1_5_checked, root5Node62Step2Chunk2_0_checked, root5Node62Step2Chunk2_1_checked, root5Node62Step2Chunk2_2_checked, root5Node62Step2Chunk2_3_checked, root5Node62Step2Chunk2_4_checked, root5Node62Step2Chunk2_5_checked, root5Node62Step2Chunk3_0_checked, root5Node62Step2Chunk3_1_checked, root5Node62Step2Chunk3_2_checked, root5Node62Step2Chunk3_3_checked, root5Node62Step2Chunk3_4_checked, root5Node62Step2Chunk3_5_checked, root5Node62Step2Chunk4_0_checked, root5Node62Step2Chunk4_1_checked, root5Node62Step2Chunk4_2_checked, root5Node62Step2Chunk4_3_checked, root5Node62Step2Chunk4_4_checked, root5Node62Step2Chunk4_5_checked, root5Node62Step2Chunk5_0_checked, root5Node62Step2Chunk5_1_checked, root5Node62Step2Chunk5_2_checked, root5Node62Step2Chunk5_3_checked, root5Node62Step2Chunk5_4_checked, root5Node62Step2Chunk5_5_checked, root5Node62Step2Chunk6_0_checked, root5Node62Step2Chunk6_1_checked, root5Node62Step2Chunk6_2_checked, root5Node62Step2Chunk6_3_checked, root5Node62Step2Chunk6_4_checked, root5Node62Step2Chunk6_5_checked, root5Node62Step2Chunk7_0_checked, root5Node62Step2Chunk7_1_checked, root5Node62Step2Chunk7_2_checked, root5Node62Step2Chunk7_3_checked, root5Node62Step2Chunk7_4_checked, root5Node62Step2Chunk7_5_checked, root5Node62Step2Chunk8_0_checked, root5Node62Step2Chunk8_1_checked, root5Node62Step2Chunk8_2_checked, root5Node62Step2Chunk8_3_checked, root5Node62Step2Chunk8_4_checked, root5Node62Step2Chunk8_5_checked, Bool.true_and])
theorem root5Node62Step2_checked :
    checkReplacement table56 root5Node62Domains1 root5Node62Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root5Node62Domains1 root5Node62Domains2
    root5Node62Domains1Fast root5Node62Domains2Fast
    root5Node62Domains1_fast_eq root5Node62Domains2_fast_eq
    root5Node62Step2Narrowing_checked (by decide)
theorem root5Node62Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node62Domains2 (.output 30) = true := by decide
def root5Node63Domains0 : Domains 91 State := restrict root5Node61Domains1 13 (7,3)
def root5Node63Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(1,4)]
  | 13 => some [(7,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5),(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0),(1,3)]
  | 41 => some [(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,4),(6,1)]
  | 52 => some [(5,1),(5,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3),(8,3)]
  | 62 => some [(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(4,2),(8,2)]
  | 72 => some [(5,0),(5,3)]
  | 73 => some [(4,5),(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(1,4),(3,4),(5,4)]
  | 80 => some [(0,0),(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(2,3),(2,5),(4,3)]
  | 86 => some [(0,2),(1,5),(6,0)]
  | 87 => some [(1,1),(6,1),(7,1)]
  | 88 => some [(4,1),(7,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root5Node63Domains0_fast_eq : root5Node63Domains0 = expandDomains root5Node63Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node63Domains0 v = expandDomains root5Node63Domains0Fast v from by decide) v
def root5Node64Domains0 : Domains 91 State := restrict root5Node63Domains0 30 (4,5)
def root5Node64Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(1,4)]
  | 13 => some [(7,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0),(1,3)]
  | 41 => some [(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,4),(6,1)]
  | 52 => some [(5,1),(5,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3),(8,3)]
  | 62 => some [(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(4,2),(8,2)]
  | 72 => some [(5,0),(5,3)]
  | 73 => some [(4,5),(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(1,4),(3,4),(5,4)]
  | 80 => some [(0,0),(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(2,3),(2,5),(4,3)]
  | 86 => some [(0,2),(1,5),(6,0)]
  | 87 => some [(1,1),(6,1),(7,1)]
  | 88 => some [(4,1),(7,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root5Node64Domains0_fast_eq : root5Node64Domains0 = expandDomains root5Node64Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node64Domains0 v = expandDomains root5Node64Domains0Fast v from by decide) v
def root5Node64Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(1,4)]
  | 13 => [(7,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(3,0)]
  | 19 => [(2,5)]
  | 20 => [(6,0)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(0,0)]
  | 28 => [(7,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(1,0)]
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
  | 76 => [(5,5),(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(0,0)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(0,5),(6,3)]
  | 84 => [(4,4),(7,2)]
  | 85 => [(4,3)]
  | 86 => [(1,5)]
  | 87 => [(6,1)]
  | 88 => [(4,1)]
  | 89 => [(0,2),(6,0)]
  | _ => [(1,1),(7,1)]
def root5Node64Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(1,4)]
  | 13 => some [(7,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
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
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(0,0)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(1,5)]
  | 87 => some [(6,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root5Node64Domains1_fast_eq : root5Node64Domains1 = expandDomains root5Node64Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node64Domains1 v = expandDomains root5Node64Domains1Fast v from by decide) v
theorem root5Node64Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq (by decide)
theorem root5Node64Step1Narrowing_checked :
    checkNarrowing table54 root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root5Node64Domains0 root5Node64Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node64Step1Chunk0_0_checked, root5Node64Step1Chunk0_1_checked, root5Node64Step1Chunk0_2_checked, root5Node64Step1Chunk0_3_checked, root5Node64Step1Chunk0_4_checked, root5Node64Step1Chunk0_5_checked, root5Node64Step1Chunk1_0_checked, root5Node64Step1Chunk1_1_checked, root5Node64Step1Chunk1_2_checked, root5Node64Step1Chunk1_3_checked, root5Node64Step1Chunk1_4_checked, root5Node64Step1Chunk1_5_checked, root5Node64Step1Chunk2_0_checked, root5Node64Step1Chunk2_1_checked, root5Node64Step1Chunk2_2_checked, root5Node64Step1Chunk2_3_checked, root5Node64Step1Chunk2_4_checked, root5Node64Step1Chunk2_5_checked, root5Node64Step1Chunk3_0_checked, root5Node64Step1Chunk3_1_checked, root5Node64Step1Chunk3_2_checked, root5Node64Step1Chunk3_3_checked, root5Node64Step1Chunk3_4_checked, root5Node64Step1Chunk3_5_checked, root5Node64Step1Chunk4_0_checked, root5Node64Step1Chunk4_1_checked, root5Node64Step1Chunk4_2_checked, root5Node64Step1Chunk4_3_checked, root5Node64Step1Chunk4_4_checked, root5Node64Step1Chunk4_5_checked, root5Node64Step1Chunk5_0_checked, root5Node64Step1Chunk5_1_checked, root5Node64Step1Chunk5_2_checked, root5Node64Step1Chunk5_3_checked, root5Node64Step1Chunk5_4_checked, root5Node64Step1Chunk5_5_checked, root5Node64Step1Chunk6_0_checked, root5Node64Step1Chunk6_1_checked, root5Node64Step1Chunk6_2_checked, root5Node64Step1Chunk6_3_checked, root5Node64Step1Chunk6_4_checked, root5Node64Step1Chunk6_5_checked, root5Node64Step1Chunk7_0_checked, root5Node64Step1Chunk7_1_checked, root5Node64Step1Chunk7_2_checked, root5Node64Step1Chunk7_3_checked, root5Node64Step1Chunk7_4_checked, root5Node64Step1Chunk7_5_checked, root5Node64Step1Chunk8_0_checked, root5Node64Step1Chunk8_1_checked, root5Node64Step1Chunk8_2_checked, root5Node64Step1Chunk8_3_checked, root5Node64Step1Chunk8_4_checked, root5Node64Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node64Step1_checked :
    checkReplacement table54 root5Node64Domains0 root5Node64Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node64Domains0 root5Node64Domains1
    root5Node64Domains0Fast root5Node64Domains1Fast
    root5Node64Domains0_fast_eq root5Node64Domains1_fast_eq
    root5Node64Step1Narrowing_checked (by decide)
def root5Node64Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(1,4)]
  | 13 => [(7,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(3,0)]
  | 19 => [(2,5)]
  | 20 => [(6,0)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(0,0)]
  | 28 => [(7,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(1,0)]
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
def root5Node64Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(1,4)]
  | 13 => some [(7,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(3,0)]
  | 19 => some [(2,5)]
  | 20 => some [(6,0)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(0,0)]
  | 28 => some [(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
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
theorem root5Node64Domains2_fast_eq : root5Node64Domains2 = expandDomains root5Node64Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node64Domains2 v = expandDomains root5Node64Domains2Fast v from by decide) v
theorem root5Node64Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq (by decide)
theorem root5Node64Step2Narrowing_checked :
    checkNarrowing table56 root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root5Node64Domains1 root5Node64Domains2 (by
      simp only [List.all_cons, List.all_nil, root5Node64Step2Chunk0_0_checked, root5Node64Step2Chunk0_1_checked, root5Node64Step2Chunk0_2_checked, root5Node64Step2Chunk0_3_checked, root5Node64Step2Chunk0_4_checked, root5Node64Step2Chunk0_5_checked, root5Node64Step2Chunk1_0_checked, root5Node64Step2Chunk1_1_checked, root5Node64Step2Chunk1_2_checked, root5Node64Step2Chunk1_3_checked, root5Node64Step2Chunk1_4_checked, root5Node64Step2Chunk1_5_checked, root5Node64Step2Chunk2_0_checked, root5Node64Step2Chunk2_1_checked, root5Node64Step2Chunk2_2_checked, root5Node64Step2Chunk2_3_checked, root5Node64Step2Chunk2_4_checked, root5Node64Step2Chunk2_5_checked, root5Node64Step2Chunk3_0_checked, root5Node64Step2Chunk3_1_checked, root5Node64Step2Chunk3_2_checked, root5Node64Step2Chunk3_3_checked, root5Node64Step2Chunk3_4_checked, root5Node64Step2Chunk3_5_checked, root5Node64Step2Chunk4_0_checked, root5Node64Step2Chunk4_1_checked, root5Node64Step2Chunk4_2_checked, root5Node64Step2Chunk4_3_checked, root5Node64Step2Chunk4_4_checked, root5Node64Step2Chunk4_5_checked, root5Node64Step2Chunk5_0_checked, root5Node64Step2Chunk5_1_checked, root5Node64Step2Chunk5_2_checked, root5Node64Step2Chunk5_3_checked, root5Node64Step2Chunk5_4_checked, root5Node64Step2Chunk5_5_checked, root5Node64Step2Chunk6_0_checked, root5Node64Step2Chunk6_1_checked, root5Node64Step2Chunk6_2_checked, root5Node64Step2Chunk6_3_checked, root5Node64Step2Chunk6_4_checked, root5Node64Step2Chunk6_5_checked, root5Node64Step2Chunk7_0_checked, root5Node64Step2Chunk7_1_checked, root5Node64Step2Chunk7_2_checked, root5Node64Step2Chunk7_3_checked, root5Node64Step2Chunk7_4_checked, root5Node64Step2Chunk7_5_checked, root5Node64Step2Chunk8_0_checked, root5Node64Step2Chunk8_1_checked, root5Node64Step2Chunk8_2_checked, root5Node64Step2Chunk8_3_checked, root5Node64Step2Chunk8_4_checked, root5Node64Step2Chunk8_5_checked, Bool.true_and])
theorem root5Node64Step2_checked :
    checkReplacement table56 root5Node64Domains1 root5Node64Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root5Node64Domains1 root5Node64Domains2
    root5Node64Domains1Fast root5Node64Domains2Fast
    root5Node64Domains1_fast_eq root5Node64Domains2_fast_eq
    root5Node64Step2Narrowing_checked (by decide)
theorem root5Node64Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node64Domains2 (.output 31) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
