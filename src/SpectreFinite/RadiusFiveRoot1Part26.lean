module

public import SpectreFinite.RadiusFiveRoot1Part25
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node62Domains0 : Domains 91 State := restrict root1Node60Domains3 5 (3,5)
def root1Node62Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(3,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(2,0),(2,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(6,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(1,0),(7,0)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0),(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1),(8,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0)]
  | 83 => some [(7,3)]
  | 84 => some [(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1)]
  | 89 => some [(0,1)]
  | _ => some [(6,2)]
theorem root1Node62Domains0_fast_eq : root1Node62Domains0 = expandDomains root1Node62Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node62Domains0 v = expandDomains root1Node62Domains0Fast v from by decide) v
def root1Node62Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(3,5)]
  | 6 => [(0,4)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(4,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(2,4)]
  | 13 => [(3,0)]
  | 14 => [(2,5)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(6,5)]
  | 21 => [(4,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(7,0)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(8,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,0)]
  | 83 => [(7,3)]
  | 84 => [(5,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(3,1)]
  | 89 => [(0,1)]
  | _ => [(6,2)]
def root1Node62Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(3,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(2,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(6,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(7,0)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0)]
  | 83 => some [(7,3)]
  | 84 => some [(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1)]
  | 89 => some [(0,1)]
  | _ => some [(6,2)]
theorem root1Node62Domains1_fast_eq : root1Node62Domains1 = expandDomains root1Node62Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node62Domains1 v = expandDomains root1Node62Domains1Fast v from by decide) v
theorem root1Node62Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq (by decide)
theorem root1Node62Step1Narrowing_checked :
    checkNarrowing table12 root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root1Node62Domains0 root1Node62Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node62Step1Chunk0_0_checked, root1Node62Step1Chunk0_1_checked, root1Node62Step1Chunk0_2_checked, root1Node62Step1Chunk0_3_checked, root1Node62Step1Chunk0_4_checked, root1Node62Step1Chunk0_5_checked, root1Node62Step1Chunk1_0_checked, root1Node62Step1Chunk1_1_checked, root1Node62Step1Chunk1_2_checked, root1Node62Step1Chunk1_3_checked, root1Node62Step1Chunk1_4_checked, root1Node62Step1Chunk1_5_checked, root1Node62Step1Chunk2_0_checked, root1Node62Step1Chunk2_1_checked, root1Node62Step1Chunk2_2_checked, root1Node62Step1Chunk2_3_checked, root1Node62Step1Chunk2_4_checked, root1Node62Step1Chunk2_5_checked, root1Node62Step1Chunk3_0_checked, root1Node62Step1Chunk3_1_checked, root1Node62Step1Chunk3_2_checked, root1Node62Step1Chunk3_3_checked, root1Node62Step1Chunk3_4_checked, root1Node62Step1Chunk3_5_checked, root1Node62Step1Chunk4_0_checked, root1Node62Step1Chunk4_1_checked, root1Node62Step1Chunk4_2_checked, root1Node62Step1Chunk4_3_checked, root1Node62Step1Chunk4_4_checked, root1Node62Step1Chunk4_5_checked, root1Node62Step1Chunk5_0_checked, root1Node62Step1Chunk5_1_checked, root1Node62Step1Chunk5_2_checked, root1Node62Step1Chunk5_3_checked, root1Node62Step1Chunk5_4_checked, root1Node62Step1Chunk5_5_checked, root1Node62Step1Chunk6_0_checked, root1Node62Step1Chunk6_1_checked, root1Node62Step1Chunk6_2_checked, root1Node62Step1Chunk6_3_checked, root1Node62Step1Chunk6_4_checked, root1Node62Step1Chunk6_5_checked, root1Node62Step1Chunk7_0_checked, root1Node62Step1Chunk7_1_checked, root1Node62Step1Chunk7_2_checked, root1Node62Step1Chunk7_3_checked, root1Node62Step1Chunk7_4_checked, root1Node62Step1Chunk7_5_checked, root1Node62Step1Chunk8_0_checked, root1Node62Step1Chunk8_1_checked, root1Node62Step1Chunk8_2_checked, root1Node62Step1Chunk8_3_checked, root1Node62Step1Chunk8_4_checked, root1Node62Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node62Step1_checked :
    checkReplacement table12 root1Node62Domains0 root1Node62Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node62Domains0 root1Node62Domains1
    root1Node62Domains0Fast root1Node62Domains1Fast
    root1Node62Domains0_fast_eq root1Node62Domains1_fast_eq
    root1Node62Step1Narrowing_checked (by decide)
theorem root1Node62Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node62Domains1 (.output 30) = true := by decide
def root1Node63Domains0 : Domains 91 State := restrict root1Node59Domains4 4 (8,3)
def root1Node63Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(1,5),(3,5),(5,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(2,0),(2,4),(4,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(1,5),(6,5),(7,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(1,0),(4,2),(7,0),(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(4,0),(7,4),(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(5,1),(8,1)]
  | 50 => some [(0,1),(1,5),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0)]
  | 59 => some [(5,3),(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3),(7,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(3,1),(7,1)]
  | 89 => some [(0,1),(1,5),(6,5)]
  | _ => some [(0,4),(6,1),(6,2)]
theorem root1Node63Domains0_fast_eq : root1Node63Domains0 = expandDomains root1Node63Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node63Domains0 v = expandDomains root1Node63Domains0Fast v from by decide) v
def root1Node63Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(0,4)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(4,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(3,0)]
  | 14 => [(2,5)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(4,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3)]
  | 29 => [(4,2),(7,0),(8,2)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5),(7,5)]
  | 48 => [(0,3),(6,1)]
  | 49 => [(8,1)]
  | 50 => [(1,5),(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(4,0),(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(4,2),(7,0)]
  | 59 => [(5,3),(8,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(0,2),(6,5)]
  | 64 => [(0,4),(1,1)]
  | 65 => [(5,1),(5,4)]
  | 66 => [(0,0),(0,1),(6,4)]
  | 67 => [(1,2),(6,2),(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3),(8,3)]
  | 71 => [(5,2),(5,5),(8,5)]
  | 72 => [(7,0),(8,0)]
  | 73 => [(4,3),(8,3)]
  | 74 => [(1,5),(3,5),(5,5),(7,5)]
  | 75 => [(0,3),(1,0),(6,1)]
  | 76 => [(2,1),(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5),(6,2),(6,3)]
  | 79 => [(4,4),(7,2),(8,4)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(6,3)]
  | 82 => [(2,0),(2,2),(2,4),(4,4)]
  | 83 => [(0,0),(1,3),(3,3),(7,3)]
  | 84 => [(3,2),(5,2)]
  | 85 => [(1,1),(7,1)]
  | 86 => [(4,1),(7,5)]
  | 87 => [(0,2),(6,0)]
  | 88 => [(1,1),(3,1),(7,1)]
  | 89 => [(0,1),(1,5),(6,5)]
  | _ => [(0,4),(6,1),(6,2)]
def root1Node63Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0)]
  | 59 => some [(5,3),(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3),(7,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(3,1),(7,1)]
  | 89 => some [(0,1),(1,5),(6,5)]
  | _ => some [(0,4),(6,1),(6,2)]
theorem root1Node63Domains1_fast_eq : root1Node63Domains1 = expandDomains root1Node63Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node63Domains1 v = expandDomains root1Node63Domains1Fast v from by decide) v
theorem root1Node63Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq (by decide)
theorem root1Node63Step1Narrowing_checked :
    checkNarrowing table12 root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root1Node63Domains0 root1Node63Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node63Step1Chunk0_0_checked, root1Node63Step1Chunk0_1_checked, root1Node63Step1Chunk0_2_checked, root1Node63Step1Chunk0_3_checked, root1Node63Step1Chunk0_4_checked, root1Node63Step1Chunk0_5_checked, root1Node63Step1Chunk1_0_checked, root1Node63Step1Chunk1_1_checked, root1Node63Step1Chunk1_2_checked, root1Node63Step1Chunk1_3_checked, root1Node63Step1Chunk1_4_checked, root1Node63Step1Chunk1_5_checked, root1Node63Step1Chunk2_0_checked, root1Node63Step1Chunk2_1_checked, root1Node63Step1Chunk2_2_checked, root1Node63Step1Chunk2_3_checked, root1Node63Step1Chunk2_4_checked, root1Node63Step1Chunk2_5_checked, root1Node63Step1Chunk3_0_checked, root1Node63Step1Chunk3_1_checked, root1Node63Step1Chunk3_2_checked, root1Node63Step1Chunk3_3_checked, root1Node63Step1Chunk3_4_checked, root1Node63Step1Chunk3_5_checked, root1Node63Step1Chunk4_0_checked, root1Node63Step1Chunk4_1_checked, root1Node63Step1Chunk4_2_checked, root1Node63Step1Chunk4_3_checked, root1Node63Step1Chunk4_4_checked, root1Node63Step1Chunk4_5_checked, root1Node63Step1Chunk5_0_checked, root1Node63Step1Chunk5_1_checked, root1Node63Step1Chunk5_2_checked, root1Node63Step1Chunk5_3_checked, root1Node63Step1Chunk5_4_checked, root1Node63Step1Chunk5_5_checked, root1Node63Step1Chunk6_0_checked, root1Node63Step1Chunk6_1_checked, root1Node63Step1Chunk6_2_checked, root1Node63Step1Chunk6_3_checked, root1Node63Step1Chunk6_4_checked, root1Node63Step1Chunk6_5_checked, root1Node63Step1Chunk7_0_checked, root1Node63Step1Chunk7_1_checked, root1Node63Step1Chunk7_2_checked, root1Node63Step1Chunk7_3_checked, root1Node63Step1Chunk7_4_checked, root1Node63Step1Chunk7_5_checked, root1Node63Step1Chunk8_0_checked, root1Node63Step1Chunk8_1_checked, root1Node63Step1Chunk8_2_checked, root1Node63Step1Chunk8_3_checked, root1Node63Step1Chunk8_4_checked, root1Node63Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node63Step1_checked :
    checkReplacement table12 root1Node63Domains0 root1Node63Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node63Domains0 root1Node63Domains1
    root1Node63Domains0Fast root1Node63Domains1Fast
    root1Node63Domains0_fast_eq root1Node63Domains1_fast_eq
    root1Node63Step1Narrowing_checked (by decide)
def root1Node64Domains0 : Domains 91 State := restrict root1Node63Domains1 20 (1,5)
def root1Node64Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0)]
  | 59 => some [(5,3),(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3),(7,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(3,1),(7,1)]
  | 89 => some [(0,1),(1,5),(6,5)]
  | _ => some [(0,4),(6,1),(6,2)]
theorem root1Node64Domains0_fast_eq : root1Node64Domains0 = expandDomains root1Node64Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node64Domains0 v = expandDomains root1Node64Domains0Fast v from by decide) v
def root1Node64Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(0,4)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(4,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(3,0)]
  | 14 => [(2,5)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5)]
  | 21 => [(4,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(7,0)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(8,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3),(8,3)]
  | 71 => [(5,2),(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5),(6,2),(6,3)]
  | 79 => [(4,4),(7,2),(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,0)]
  | 83 => [(7,3)]
  | 84 => [(5,2)]
  | 85 => [(1,1),(7,1)]
  | 86 => [(4,1),(7,5)]
  | 87 => [(6,0)]
  | 88 => [(3,1)]
  | 89 => [(0,1)]
  | _ => [(6,2)]
def root1Node64Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(7,0)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(7,2),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0)]
  | 83 => some [(7,3)]
  | 84 => some [(5,2)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1)]
  | 89 => some [(0,1)]
  | _ => some [(6,2)]
theorem root1Node64Domains1_fast_eq : root1Node64Domains1 = expandDomains root1Node64Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node64Domains1 v = expandDomains root1Node64Domains1Fast v from by decide) v
theorem root1Node64Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq (by decide)
theorem root1Node64Step1Narrowing_checked :
    checkNarrowing table57 root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root1Node64Domains0 root1Node64Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node64Step1Chunk0_0_checked, root1Node64Step1Chunk0_1_checked, root1Node64Step1Chunk0_2_checked, root1Node64Step1Chunk0_3_checked, root1Node64Step1Chunk0_4_checked, root1Node64Step1Chunk0_5_checked, root1Node64Step1Chunk1_0_checked, root1Node64Step1Chunk1_1_checked, root1Node64Step1Chunk1_2_checked, root1Node64Step1Chunk1_3_checked, root1Node64Step1Chunk1_4_checked, root1Node64Step1Chunk1_5_checked, root1Node64Step1Chunk2_0_checked, root1Node64Step1Chunk2_1_checked, root1Node64Step1Chunk2_2_checked, root1Node64Step1Chunk2_3_checked, root1Node64Step1Chunk2_4_checked, root1Node64Step1Chunk2_5_checked, root1Node64Step1Chunk3_0_checked, root1Node64Step1Chunk3_1_checked, root1Node64Step1Chunk3_2_checked, root1Node64Step1Chunk3_3_checked, root1Node64Step1Chunk3_4_checked, root1Node64Step1Chunk3_5_checked, root1Node64Step1Chunk4_0_checked, root1Node64Step1Chunk4_1_checked, root1Node64Step1Chunk4_2_checked, root1Node64Step1Chunk4_3_checked, root1Node64Step1Chunk4_4_checked, root1Node64Step1Chunk4_5_checked, root1Node64Step1Chunk5_0_checked, root1Node64Step1Chunk5_1_checked, root1Node64Step1Chunk5_2_checked, root1Node64Step1Chunk5_3_checked, root1Node64Step1Chunk5_4_checked, root1Node64Step1Chunk5_5_checked, root1Node64Step1Chunk6_0_checked, root1Node64Step1Chunk6_1_checked, root1Node64Step1Chunk6_2_checked, root1Node64Step1Chunk6_3_checked, root1Node64Step1Chunk6_4_checked, root1Node64Step1Chunk6_5_checked, root1Node64Step1Chunk7_0_checked, root1Node64Step1Chunk7_1_checked, root1Node64Step1Chunk7_2_checked, root1Node64Step1Chunk7_3_checked, root1Node64Step1Chunk7_4_checked, root1Node64Step1Chunk7_5_checked, root1Node64Step1Chunk8_0_checked, root1Node64Step1Chunk8_1_checked, root1Node64Step1Chunk8_2_checked, root1Node64Step1Chunk8_3_checked, root1Node64Step1Chunk8_4_checked, root1Node64Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node64Step1_checked :
    checkReplacement table57 root1Node64Domains0 root1Node64Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node64Domains0 root1Node64Domains1
    root1Node64Domains0Fast root1Node64Domains1Fast
    root1Node64Domains0_fast_eq root1Node64Domains1_fast_eq
    root1Node64Step1Narrowing_checked (by decide)
def root1Node64Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(0,4)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(4,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(3,0)]
  | 14 => [(2,5)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5)]
  | 21 => [(4,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(7,0)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(8,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,0)]
  | 83 => [(7,3)]
  | 84 => [(5,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(3,1)]
  | 89 => [(0,1)]
  | _ => [(6,2)]
def root1Node64Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(4,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(3,0)]
  | 14 => some [(2,5)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(7,0)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0)]
  | 83 => some [(7,3)]
  | 84 => some [(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1)]
  | 89 => some [(0,1)]
  | _ => some [(6,2)]
theorem root1Node64Domains2_fast_eq : root1Node64Domains2 = expandDomains root1Node64Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node64Domains2 v = expandDomains root1Node64Domains2Fast v from by decide) v
theorem root1Node64Step2Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq (by decide)
theorem root1Node64Step2Narrowing_checked :
    checkNarrowing table52 root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root1Node64Domains1 root1Node64Domains2 (by
      simp only [List.all_cons, List.all_nil, root1Node64Step2Chunk0_0_checked, root1Node64Step2Chunk0_1_checked, root1Node64Step2Chunk0_2_checked, root1Node64Step2Chunk0_3_checked, root1Node64Step2Chunk0_4_checked, root1Node64Step2Chunk0_5_checked, root1Node64Step2Chunk1_0_checked, root1Node64Step2Chunk1_1_checked, root1Node64Step2Chunk1_2_checked, root1Node64Step2Chunk1_3_checked, root1Node64Step2Chunk1_4_checked, root1Node64Step2Chunk1_5_checked, root1Node64Step2Chunk2_0_checked, root1Node64Step2Chunk2_1_checked, root1Node64Step2Chunk2_2_checked, root1Node64Step2Chunk2_3_checked, root1Node64Step2Chunk2_4_checked, root1Node64Step2Chunk2_5_checked, root1Node64Step2Chunk3_0_checked, root1Node64Step2Chunk3_1_checked, root1Node64Step2Chunk3_2_checked, root1Node64Step2Chunk3_3_checked, root1Node64Step2Chunk3_4_checked, root1Node64Step2Chunk3_5_checked, root1Node64Step2Chunk4_0_checked, root1Node64Step2Chunk4_1_checked, root1Node64Step2Chunk4_2_checked, root1Node64Step2Chunk4_3_checked, root1Node64Step2Chunk4_4_checked, root1Node64Step2Chunk4_5_checked, root1Node64Step2Chunk5_0_checked, root1Node64Step2Chunk5_1_checked, root1Node64Step2Chunk5_2_checked, root1Node64Step2Chunk5_3_checked, root1Node64Step2Chunk5_4_checked, root1Node64Step2Chunk5_5_checked, root1Node64Step2Chunk6_0_checked, root1Node64Step2Chunk6_1_checked, root1Node64Step2Chunk6_2_checked, root1Node64Step2Chunk6_3_checked, root1Node64Step2Chunk6_4_checked, root1Node64Step2Chunk6_5_checked, root1Node64Step2Chunk7_0_checked, root1Node64Step2Chunk7_1_checked, root1Node64Step2Chunk7_2_checked, root1Node64Step2Chunk7_3_checked, root1Node64Step2Chunk7_4_checked, root1Node64Step2Chunk7_5_checked, root1Node64Step2Chunk8_0_checked, root1Node64Step2Chunk8_1_checked, root1Node64Step2Chunk8_2_checked, root1Node64Step2Chunk8_3_checked, root1Node64Step2Chunk8_4_checked, root1Node64Step2Chunk8_5_checked, Bool.true_and])
theorem root1Node64Step2_checked :
    checkReplacement table52 root1Node64Domains1 root1Node64Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root1Node64Domains1 root1Node64Domains2
    root1Node64Domains1Fast root1Node64Domains2Fast
    root1Node64Domains1_fast_eq root1Node64Domains2_fast_eq
    root1Node64Step2Narrowing_checked (by decide)
theorem root1Node64Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node64Domains2 (.output 31) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
