module

public import SpectreFinite.RadiusFiveRoot7Part42
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable19
public import SpectreFinite.RadiusFiveTable31
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable52

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node109Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,2)]
  | 1 => [(7,4)]
  | 2 => [(1,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(5,5)]
  | 6 => [(6,1)]
  | 7 => [(8,1)]
  | 8 => [(6,5)]
  | 9 => [(0,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(7,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(4,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(7,5)]
  | 51 => [(0,1)]
  | 52 => [(6,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(8,2)]
  | 59 => [(8,0)]
  | 60 => [(7,3)]
  | 61 => [(1,0)]
  | 62 => [(7,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(5,4)]
  | 69 => [(6,4)]
  | 70 => [(5,0)]
  | 71 => [(4,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(7,5)]
  | 78 => [(0,0)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(6,3)]
  | 82 => [(7,2)]
  | 83 => [(7,4)]
  | 84 => [(6,3)]
  | 85 => [(6,1)]
  | 86 => [(4,1)]
  | 87 => [(0,2)]
  | 88 => [(1,1)]
  | 89 => [(4,1)]
  | _ => [(0,2)]
def root7Node109Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(1,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(5,5)]
  | 6 => some [(6,1)]
  | 7 => some [(8,1)]
  | 8 => some [(6,5)]
  | 9 => some [(0,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(7,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(4,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(7,5)]
  | 51 => some [(0,1)]
  | 52 => some [(6,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(8,0)]
  | 60 => some [(7,3)]
  | 61 => some [(1,0)]
  | 62 => some [(7,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(6,4)]
  | 70 => some [(5,0)]
  | 71 => some [(4,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(7,5)]
  | 78 => some [(0,0)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(6,3)]
  | 82 => some [(7,2)]
  | 83 => some [(7,4)]
  | 84 => some [(6,3)]
  | 85 => some [(6,1)]
  | 86 => some [(4,1)]
  | 87 => some [(0,2)]
  | 88 => some [(1,1)]
  | 89 => some [(4,1)]
  | _ => some [(0,2)]
theorem root7Node109Domains3_fast_eq : root7Node109Domains3 = expandDomains root7Node109Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node109Domains3 v = expandDomains root7Node109Domains3Fast v from by decide) v
theorem root7Node109Step3Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq (by decide)
theorem root7Node109Step3Narrowing_checked :
    checkNarrowing table19 root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkNarrowing_flatten table19Scope [table19Rows0_0,table19Rows0_1,table19Rows0_2,table19Rows0_3,table19Rows0_4,table19Rows0_5,table19Rows1_0,table19Rows1_1,table19Rows1_2,table19Rows1_3,table19Rows1_4,table19Rows1_5,table19Rows2_0,table19Rows2_1,table19Rows2_2,table19Rows2_3,table19Rows2_4,table19Rows2_5,table19Rows3_0,table19Rows3_1,table19Rows3_2,table19Rows3_3,table19Rows3_4,table19Rows3_5,table19Rows4_0,table19Rows4_1,table19Rows4_2,table19Rows4_3,table19Rows4_4,table19Rows4_5,table19Rows5_0,table19Rows5_1,table19Rows5_2,table19Rows5_3,table19Rows5_4,table19Rows5_5,table19Rows6_0,table19Rows6_1,table19Rows6_2,table19Rows6_3,table19Rows6_4,table19Rows6_5,table19Rows7_0,table19Rows7_1,table19Rows7_2,table19Rows7_3,table19Rows7_4,table19Rows7_5,table19Rows8_0,table19Rows8_1,table19Rows8_2,table19Rows8_3,table19Rows8_4,table19Rows8_5]
    root7Node109Domains2 root7Node109Domains3 (by
      simp only [List.all_cons, List.all_nil, root7Node109Step3Chunk0_0_checked, root7Node109Step3Chunk0_1_checked, root7Node109Step3Chunk0_2_checked, root7Node109Step3Chunk0_3_checked, root7Node109Step3Chunk0_4_checked, root7Node109Step3Chunk0_5_checked, root7Node109Step3Chunk1_0_checked, root7Node109Step3Chunk1_1_checked, root7Node109Step3Chunk1_2_checked, root7Node109Step3Chunk1_3_checked, root7Node109Step3Chunk1_4_checked, root7Node109Step3Chunk1_5_checked, root7Node109Step3Chunk2_0_checked, root7Node109Step3Chunk2_1_checked, root7Node109Step3Chunk2_2_checked, root7Node109Step3Chunk2_3_checked, root7Node109Step3Chunk2_4_checked, root7Node109Step3Chunk2_5_checked, root7Node109Step3Chunk3_0_checked, root7Node109Step3Chunk3_1_checked, root7Node109Step3Chunk3_2_checked, root7Node109Step3Chunk3_3_checked, root7Node109Step3Chunk3_4_checked, root7Node109Step3Chunk3_5_checked, root7Node109Step3Chunk4_0_checked, root7Node109Step3Chunk4_1_checked, root7Node109Step3Chunk4_2_checked, root7Node109Step3Chunk4_3_checked, root7Node109Step3Chunk4_4_checked, root7Node109Step3Chunk4_5_checked, root7Node109Step3Chunk5_0_checked, root7Node109Step3Chunk5_1_checked, root7Node109Step3Chunk5_2_checked, root7Node109Step3Chunk5_3_checked, root7Node109Step3Chunk5_4_checked, root7Node109Step3Chunk5_5_checked, root7Node109Step3Chunk6_0_checked, root7Node109Step3Chunk6_1_checked, root7Node109Step3Chunk6_2_checked, root7Node109Step3Chunk6_3_checked, root7Node109Step3Chunk6_4_checked, root7Node109Step3Chunk6_5_checked, root7Node109Step3Chunk7_0_checked, root7Node109Step3Chunk7_1_checked, root7Node109Step3Chunk7_2_checked, root7Node109Step3Chunk7_3_checked, root7Node109Step3Chunk7_4_checked, root7Node109Step3Chunk7_5_checked, root7Node109Step3Chunk8_0_checked, root7Node109Step3Chunk8_1_checked, root7Node109Step3Chunk8_2_checked, root7Node109Step3Chunk8_3_checked, root7Node109Step3Chunk8_4_checked, root7Node109Step3Chunk8_5_checked, Bool.true_and])
theorem root7Node109Step3_checked :
    checkReplacement table19 root7Node109Domains2 root7Node109Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root7Node109Domains2 root7Node109Domains3
    root7Node109Domains2Fast root7Node109Domains3Fast
    root7Node109Domains2_fast_eq root7Node109Domains3_fast_eq
    root7Node109Step3Narrowing_checked (by decide)
theorem root7Node109Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node109Domains3 (.output 54) = true := by decide
def root7Node110Domains0 : Domains 91 State := restrict root7Node0Domains4 25 (1,3)
def root7Node110Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(4,4),(7,2),(7,4),(8,2),(8,4)]
  | 1 => some [(0,0),(1,3),(1,4),(4,0),(6,4),(7,4),(8,0)]
  | 2 => some [(0,5),(1,2),(1,3),(3,2),(5,2),(6,3),(7,2),(7,3),(8,2)]
  | 3 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(8,0)]
  | 4 => some [(0,0),(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 5 => some [(3,2),(4,2),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 6 => some [(0,4),(1,1),(6,1),(7,1),(8,1)]
  | 7 => some [(1,5),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 8 => some [(0,1),(0,2),(0,3),(0,4),(6,0),(6,1),(6,4),(6,5)]
  | 9 => some [(0,4),(1,1),(1,2),(3,1),(5,1),(5,4),(6,2),(7,1)]
  | 10 => some [(0,1),(1,4),(1,5),(6,4),(6,5),(7,4)]
  | 11 => some [(0,4),(0,5),(1,2),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(7,4),(8,4)]
  | 13 => some [(4,0),(5,0),(5,3),(7,0),(8,0),(8,3)]
  | 14 => some [(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 15 => some [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 16 => some [(0,3),(1,0),(3,0),(4,3),(5,0),(5,3),(8,3)]
  | 17 => some [(2,1),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 18 => some [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(7,1),(8,1),(8,3)]
  | 20 => some [(1,5),(4,1),(5,1),(6,5),(7,5),(8,1),(8,5)]
  | 21 => some [(4,4),(5,1),(5,4),(7,4),(8,4)]
  | 22 => some [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 23 => some [(0,5),(1,2),(6,2),(7,2)]
  | 24 => some [(2,4),(4,4),(7,4),(8,4)]
  | 25 => some [(1,3)]
  | 26 => some [(3,2),(4,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 28 => some [(1,3),(4,5),(7,3),(8,3),(8,5)]
  | 29 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 30 => some [(4,1),(4,3),(5,3),(7,1),(8,1),(8,3)]
  | 31 => some [(0,2),(1,5),(7,5),(8,5)]
  | 32 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 33 => some [(7,1),(8,1)]
  | 34 => some [(1,5),(6,5)]
  | 35 => some [(0,4),(6,1)]
  | 36 => some [(3,4),(5,1),(5,4),(8,1)]
  | 37 => some [(0,0),(0,1),(1,4),(6,3),(6,4),(6,5)]
  | 38 => some [(0,4),(0,5),(1,2),(6,2),(7,2)]
  | 39 => some [(1,4),(3,4),(4,4),(5,4),(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(7,4),(8,0)]
  | 41 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(7,0),(8,0),(8,2)]
  | 43 => some [(5,0),(5,3),(8,3)]
  | 44 => some [(4,5),(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3),(8,3)]
  | 47 => some [(0,2),(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 48 => some [(0,3),(1,0),(1,1),(3,0),(6,0),(6,1),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 50 => some [(0,2),(1,5),(3,5),(6,0),(6,5),(7,5)]
  | 51 => some [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,3),(1,4),(3,3),(4,0),(5,0),(5,3),(6,4),(7,3),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(5,2),(5,5),(6,3),(7,2),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(1,5),(3,4),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4),(7,3)]
  | 71 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 72 => some [(2,0),(4,0),(7,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
  | 76 => some [(2,3),(2,5),(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 77 => some [(0,2),(1,0),(1,5),(3,5),(4,2),(5,2),(5,5),(6,0),(7,0),(7,5),(8,2)]
  | 78 => some [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4),(7,4)]
  | 81 => some [(0,5),(1,2),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => some [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(3,5),(4,1),(4,5),(7,5),(8,5)]
  | 87 => some [(0,2),(0,3),(1,0),(6,0)]
  | 88 => some [(1,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
theorem root7Node110Domains0_fast_eq : root7Node110Domains0 = expandDomains root7Node110Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node110Domains0 v = expandDomains root7Node110Domains0Fast v from by decide) v
def root7Node110Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,2),(7,4),(8,2),(8,4)]
  | 1 => [(0,0),(1,3),(1,4),(4,0),(6,4),(7,4),(8,0)]
  | 2 => [(1,2),(3,2),(5,2),(7,2),(7,3),(8,2)]
  | 3 => [(4,0),(4,2),(8,0)]
  | 4 => [(5,3),(7,3),(8,3)]
  | 5 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 6 => [(0,4),(1,1),(6,1),(7,1),(8,1)]
  | 7 => [(1,5),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 8 => [(0,3),(0,4),(6,1),(6,4)]
  | 9 => [(1,2),(5,1),(5,4)]
  | 10 => [(0,1),(1,4),(6,4),(7,4)]
  | 11 => [(0,5),(1,2),(6,2),(6,3)]
  | 12 => [(4,4),(7,2),(7,4),(8,4)]
  | 13 => [(4,0),(5,0),(5,3),(7,0),(8,0),(8,3)]
  | 14 => [(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 15 => [(3,5),(4,2),(7,0)]
  | 16 => [(0,3),(4,3),(5,3),(8,3)]
  | 17 => [(4,1),(7,5),(8,5)]
  | 18 => [(0,2),(0,3),(1,0),(6,0)]
  | 19 => [(1,1),(7,1),(8,1)]
  | 20 => [(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 21 => [(4,4),(5,1),(5,4),(7,4),(8,4)]
  | 22 => [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 23 => [(0,5),(1,2),(7,2)]
  | 24 => [(2,4),(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2),(5,2),(8,2)]
  | 27 => [(5,0),(5,3),(8,0)]
  | 28 => [(4,5),(7,3),(8,3),(8,5)]
  | 29 => [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 30 => [(4,1),(4,3),(5,3),(7,1),(8,1),(8,3)]
  | 31 => [(0,2),(1,5),(7,5),(8,5)]
  | 32 => [(0,3),(1,1),(6,0),(6,1)]
  | 33 => [(7,1),(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(3,4),(5,4)]
  | 37 => [(0,0),(1,4),(6,3),(6,4)]
  | 38 => [(0,5),(1,2),(7,2)]
  | 39 => [(4,4),(7,4),(8,4)]
  | 40 => [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(7,4),(8,0)]
  | 41 => [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => [(4,2),(7,0),(8,0),(8,2)]
  | 43 => [(5,0),(5,3),(8,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3),(4,3)]
  | 47 => [(0,2),(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(1,1),(6,0),(6,1)]
  | 49 => [(4,1),(7,1),(8,1)]
  | 50 => [(0,2),(1,5),(6,5),(7,5)]
  | 51 => [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => [(0,0),(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(6,4),(7,4)]
  | 57 => [(0,5),(1,2),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,0),(4,2),(8,2)]
  | 59 => [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 60 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 61 => [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 63 => [(0,2),(1,5),(6,0)]
  | 64 => [(1,1),(6,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(0,3),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(5,4),(6,5)]
  | 69 => [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 70 => [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4),(7,3)]
  | 71 => [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 72 => [(2,0),(4,0),(7,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 75 => [(3,0),(5,0),(5,3),(7,0)]
  | 76 => [(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 77 => [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0),(7,5)]
  | 78 => [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => [(0,1),(1,4),(6,4),(7,4)]
  | 81 => [(0,5),(1,2),(6,2),(6,3)]
  | 82 => [(4,4),(7,2),(7,4),(8,4)]
  | 83 => [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => [(3,5),(4,1),(4,5),(7,5),(8,5)]
  | 87 => [(0,2),(0,3),(1,0),(6,0)]
  | 88 => [(1,1),(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
def root7Node110Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(4,4),(7,2),(7,4),(8,2),(8,4)]
  | 1 => some [(0,0),(1,3),(1,4),(4,0),(6,4),(7,4),(8,0)]
  | 2 => some [(1,2),(3,2),(5,2),(7,2),(7,3),(8,2)]
  | 3 => some [(4,0),(4,2),(8,0)]
  | 4 => some [(5,3),(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 6 => some [(0,4),(1,1),(6,1),(7,1),(8,1)]
  | 7 => some [(1,5),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 8 => some [(0,3),(0,4),(6,1),(6,4)]
  | 9 => some [(1,2),(5,1),(5,4)]
  | 10 => some [(0,1),(1,4),(6,4),(7,4)]
  | 11 => some [(0,5),(1,2),(6,2),(6,3)]
  | 12 => some [(4,4),(7,2),(7,4),(8,4)]
  | 13 => some [(4,0),(5,0),(5,3),(7,0),(8,0),(8,3)]
  | 14 => some [(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 15 => some [(3,5),(4,2),(7,0)]
  | 16 => some [(0,3),(4,3),(5,3),(8,3)]
  | 17 => some [(4,1),(7,5),(8,5)]
  | 18 => some [(0,2),(0,3),(1,0),(6,0)]
  | 19 => some [(1,1),(7,1),(8,1)]
  | 20 => some [(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 21 => some [(4,4),(5,1),(5,4),(7,4),(8,4)]
  | 22 => some [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 23 => some [(0,5),(1,2),(7,2)]
  | 24 => some [(2,4),(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2),(5,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,3),(8,5)]
  | 29 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 30 => some [(4,1),(4,3),(5,3),(7,1),(8,1),(8,3)]
  | 31 => some [(0,2),(1,5),(7,5),(8,5)]
  | 32 => some [(0,3),(1,1),(6,0),(6,1)]
  | 33 => some [(7,1),(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4),(5,4)]
  | 37 => some [(0,0),(1,4),(6,3),(6,4)]
  | 38 => some [(0,5),(1,2),(7,2)]
  | 39 => some [(4,4),(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(7,4),(8,0)]
  | 41 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(7,0),(8,0),(8,2)]
  | 43 => some [(5,0),(5,3),(8,3)]
  | 44 => some [(4,5),(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3)]
  | 47 => some [(0,2),(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,0),(6,1)]
  | 49 => some [(4,1),(7,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5),(7,5)]
  | 51 => some [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(8,2)]
  | 59 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 60 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(5,4),(6,5)]
  | 69 => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4),(7,3)]
  | 71 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 72 => some [(2,0),(4,0),(7,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0)]
  | 76 => some [(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 77 => some [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0),(7,5)]
  | 78 => some [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4),(7,4)]
  | 81 => some [(0,5),(1,2),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => some [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(3,5),(4,1),(4,5),(7,5),(8,5)]
  | 87 => some [(0,2),(0,3),(1,0),(6,0)]
  | 88 => some [(1,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
theorem root7Node110Domains1_fast_eq : root7Node110Domains1 = expandDomains root7Node110Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node110Domains1 v = expandDomains root7Node110Domains1Fast v from by decide) v
theorem root7Node110Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq (by decide)
theorem root7Node110Step1Narrowing_checked :
    checkNarrowing table36 root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root7Node110Domains0 root7Node110Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node110Step1Chunk0_0_checked, root7Node110Step1Chunk0_1_checked, root7Node110Step1Chunk0_2_checked, root7Node110Step1Chunk0_3_checked, root7Node110Step1Chunk0_4_checked, root7Node110Step1Chunk0_5_checked, root7Node110Step1Chunk1_0_checked, root7Node110Step1Chunk1_1_checked, root7Node110Step1Chunk1_2_checked, root7Node110Step1Chunk1_3_checked, root7Node110Step1Chunk1_4_checked, root7Node110Step1Chunk1_5_checked, root7Node110Step1Chunk2_0_checked, root7Node110Step1Chunk2_1_checked, root7Node110Step1Chunk2_2_checked, root7Node110Step1Chunk2_3_checked, root7Node110Step1Chunk2_4_checked, root7Node110Step1Chunk2_5_checked, root7Node110Step1Chunk3_0_checked, root7Node110Step1Chunk3_1_checked, root7Node110Step1Chunk3_2_checked, root7Node110Step1Chunk3_3_checked, root7Node110Step1Chunk3_4_checked, root7Node110Step1Chunk3_5_checked, root7Node110Step1Chunk4_0_checked, root7Node110Step1Chunk4_1_checked, root7Node110Step1Chunk4_2_checked, root7Node110Step1Chunk4_3_checked, root7Node110Step1Chunk4_4_checked, root7Node110Step1Chunk4_5_checked, root7Node110Step1Chunk5_0_checked, root7Node110Step1Chunk5_1_checked, root7Node110Step1Chunk5_2_checked, root7Node110Step1Chunk5_3_checked, root7Node110Step1Chunk5_4_checked, root7Node110Step1Chunk5_5_checked, root7Node110Step1Chunk6_0_checked, root7Node110Step1Chunk6_1_checked, root7Node110Step1Chunk6_2_checked, root7Node110Step1Chunk6_3_checked, root7Node110Step1Chunk6_4_checked, root7Node110Step1Chunk6_5_checked, root7Node110Step1Chunk7_0_checked, root7Node110Step1Chunk7_1_checked, root7Node110Step1Chunk7_2_checked, root7Node110Step1Chunk7_3_checked, root7Node110Step1Chunk7_4_checked, root7Node110Step1Chunk7_5_checked, root7Node110Step1Chunk8_0_checked, root7Node110Step1Chunk8_1_checked, root7Node110Step1Chunk8_2_checked, root7Node110Step1Chunk8_3_checked, root7Node110Step1Chunk8_4_checked, root7Node110Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node110Step1_checked :
    checkReplacement table36 root7Node110Domains0 root7Node110Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node110Domains0 root7Node110Domains1
    root7Node110Domains0Fast root7Node110Domains1Fast
    root7Node110Domains0_fast_eq root7Node110Domains1_fast_eq
    root7Node110Step1Narrowing_checked (by decide)
def root7Node110Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,4),(8,2),(8,4)]
  | 1 => [(0,0),(1,3),(6,4),(8,0)]
  | 2 => [(1,2),(3,2),(5,2),(7,2),(7,3),(8,2)]
  | 3 => [(4,0),(4,2),(8,0)]
  | 4 => [(5,3),(7,3),(8,3)]
  | 5 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 6 => [(0,4),(7,1),(8,1)]
  | 7 => [(1,5),(5,4),(6,5),(7,5)]
  | 8 => [(0,3),(0,4),(6,1),(6,4)]
  | 9 => [(1,2),(5,1),(5,4)]
  | 10 => [(0,1),(1,4),(6,4),(7,4)]
  | 11 => [(0,5),(1,2),(6,2),(6,3)]
  | 12 => [(4,4),(7,2),(7,4),(8,4)]
  | 13 => [(5,0),(5,3),(7,0),(8,0),(8,3)]
  | 14 => [(4,3),(4,5),(7,3),(8,5)]
  | 15 => [(3,5),(4,2),(7,0)]
  | 16 => [(0,3),(4,3),(5,3),(8,3)]
  | 17 => [(4,1),(7,5),(8,5)]
  | 18 => [(0,2),(0,3),(1,0),(6,0)]
  | 19 => [(1,1),(7,1),(8,1)]
  | 20 => [(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 21 => [(4,4),(5,4),(7,4),(8,4)]
  | 22 => [(0,0),(1,4),(6,3),(6,4)]
  | 23 => [(0,5),(1,2),(7,2)]
  | 24 => [(2,4),(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2),(5,2),(8,2)]
  | 27 => [(5,0),(5,3),(8,0)]
  | 28 => [(4,5),(7,3),(8,3),(8,5)]
  | 29 => [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 30 => [(4,1),(4,3),(7,1),(8,1)]
  | 31 => [(0,2),(1,5),(7,5)]
  | 32 => [(0,3),(1,1),(6,0),(6,1)]
  | 33 => [(7,1),(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(3,4),(5,4)]
  | 37 => [(0,0),(1,4),(6,3),(6,4)]
  | 38 => [(0,5),(1,2),(7,2)]
  | 39 => [(4,4),(7,4),(8,4)]
  | 40 => [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(7,4),(8,0)]
  | 41 => [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => [(4,2),(7,0),(8,0),(8,2)]
  | 43 => [(5,0),(5,3),(8,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3),(4,3)]
  | 47 => [(0,2),(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(1,1),(6,0),(6,1)]
  | 49 => [(4,1),(7,1),(8,1)]
  | 50 => [(0,2),(1,5),(6,5),(7,5)]
  | 51 => [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => [(1,4),(3,4),(7,4),(8,4)]
  | 54 => [(0,0),(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(6,4),(7,4)]
  | 57 => [(0,5),(1,2),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,0),(4,2),(8,2)]
  | 59 => [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 60 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 61 => [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(7,1),(7,5),(8,1)]
  | 63 => [(0,2),(1,5),(6,0)]
  | 64 => [(1,1),(6,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(0,3),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(5,4),(6,5)]
  | 69 => [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 70 => [(0,0),(1,3),(3,3),(5,0),(5,3),(6,4),(7,3)]
  | 71 => [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 72 => [(4,0),(7,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 75 => [(3,0),(5,0),(5,3),(7,0)]
  | 76 => [(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 77 => [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0),(7,5)]
  | 78 => [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => [(0,1),(1,4),(6,4),(7,4)]
  | 81 => [(0,5),(1,2),(6,2),(6,3)]
  | 82 => [(4,4),(7,2),(7,4),(8,4)]
  | 83 => [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => [(3,5),(4,1),(4,5),(7,5),(8,5)]
  | 87 => [(0,2),(0,3),(1,0),(6,0)]
  | 88 => [(1,1),(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
def root7Node110Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(4,4),(7,4),(8,2),(8,4)]
  | 1 => some [(0,0),(1,3),(6,4),(8,0)]
  | 2 => some [(1,2),(3,2),(5,2),(7,2),(7,3),(8,2)]
  | 3 => some [(4,0),(4,2),(8,0)]
  | 4 => some [(5,3),(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 6 => some [(0,4),(7,1),(8,1)]
  | 7 => some [(1,5),(5,4),(6,5),(7,5)]
  | 8 => some [(0,3),(0,4),(6,1),(6,4)]
  | 9 => some [(1,2),(5,1),(5,4)]
  | 10 => some [(0,1),(1,4),(6,4),(7,4)]
  | 11 => some [(0,5),(1,2),(6,2),(6,3)]
  | 12 => some [(4,4),(7,2),(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(7,0),(8,0),(8,3)]
  | 14 => some [(4,3),(4,5),(7,3),(8,5)]
  | 15 => some [(3,5),(4,2),(7,0)]
  | 16 => some [(0,3),(4,3),(5,3),(8,3)]
  | 17 => some [(4,1),(7,5),(8,5)]
  | 18 => some [(0,2),(0,3),(1,0),(6,0)]
  | 19 => some [(1,1),(7,1),(8,1)]
  | 20 => some [(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 21 => some [(4,4),(5,4),(7,4),(8,4)]
  | 22 => some [(0,0),(1,4),(6,3),(6,4)]
  | 23 => some [(0,5),(1,2),(7,2)]
  | 24 => some [(2,4),(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2),(5,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,3),(8,5)]
  | 29 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 30 => some [(4,1),(4,3),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5),(7,5)]
  | 32 => some [(0,3),(1,1),(6,0),(6,1)]
  | 33 => some [(7,1),(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4),(5,4)]
  | 37 => some [(0,0),(1,4),(6,3),(6,4)]
  | 38 => some [(0,5),(1,2),(7,2)]
  | 39 => some [(4,4),(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(7,4),(8,0)]
  | 41 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(7,0),(8,0),(8,2)]
  | 43 => some [(5,0),(5,3),(8,3)]
  | 44 => some [(4,5),(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3)]
  | 47 => some [(0,2),(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,0),(6,1)]
  | 49 => some [(4,1),(7,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5),(7,5)]
  | 51 => some [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => some [(1,4),(3,4),(7,4),(8,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(8,2)]
  | 59 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 60 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(7,1),(7,5),(8,1)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(5,4),(6,5)]
  | 69 => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 70 => some [(0,0),(1,3),(3,3),(5,0),(5,3),(6,4),(7,3)]
  | 71 => some [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 72 => some [(4,0),(7,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0)]
  | 76 => some [(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 77 => some [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0),(7,5)]
  | 78 => some [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4),(7,4)]
  | 81 => some [(0,5),(1,2),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => some [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(3,5),(4,1),(4,5),(7,5),(8,5)]
  | 87 => some [(0,2),(0,3),(1,0),(6,0)]
  | 88 => some [(1,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
theorem root7Node110Domains2_fast_eq : root7Node110Domains2 = expandDomains root7Node110Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node110Domains2 v = expandDomains root7Node110Domains2Fast v from by decide) v
theorem root7Node110Step2Chunk0_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_0⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk0_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_1⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk0_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_2⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk0_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_3⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk0_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_4⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk0_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_5⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk1_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_0⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk1_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_1⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk1_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_2⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk1_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_3⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk1_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_4⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk1_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_5⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk2_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_0⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk2_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_1⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk2_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_2⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk2_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_3⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk2_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_4⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk2_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_5⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk3_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_0⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk3_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_1⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk3_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_2⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk3_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_3⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk3_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_4⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk3_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_5⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk4_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_0⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk4_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_1⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk4_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_2⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk4_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_3⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk4_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_4⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk4_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_5⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk5_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_0⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk5_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_1⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk5_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_2⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk5_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_3⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk5_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_4⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk5_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_5⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk6_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_0⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk6_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_1⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk6_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_2⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk6_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_3⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk6_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_4⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk6_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_5⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk7_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_0⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk7_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_1⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk7_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_2⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk7_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_3⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk7_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_4⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk7_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_5⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk8_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_0⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk8_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_1⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk8_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_2⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk8_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_3⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk8_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_4⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Chunk8_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_5⟩
      root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq (by decide)
theorem root7Node110Step2Narrowing_checked :
    checkNarrowing table31 root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkNarrowing_flatten table31Scope [table31Rows0_0,table31Rows0_1,table31Rows0_2,table31Rows0_3,table31Rows0_4,table31Rows0_5,table31Rows1_0,table31Rows1_1,table31Rows1_2,table31Rows1_3,table31Rows1_4,table31Rows1_5,table31Rows2_0,table31Rows2_1,table31Rows2_2,table31Rows2_3,table31Rows2_4,table31Rows2_5,table31Rows3_0,table31Rows3_1,table31Rows3_2,table31Rows3_3,table31Rows3_4,table31Rows3_5,table31Rows4_0,table31Rows4_1,table31Rows4_2,table31Rows4_3,table31Rows4_4,table31Rows4_5,table31Rows5_0,table31Rows5_1,table31Rows5_2,table31Rows5_3,table31Rows5_4,table31Rows5_5,table31Rows6_0,table31Rows6_1,table31Rows6_2,table31Rows6_3,table31Rows6_4,table31Rows6_5,table31Rows7_0,table31Rows7_1,table31Rows7_2,table31Rows7_3,table31Rows7_4,table31Rows7_5,table31Rows8_0,table31Rows8_1,table31Rows8_2,table31Rows8_3,table31Rows8_4,table31Rows8_5]
    root7Node110Domains1 root7Node110Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node110Step2Chunk0_0_checked, root7Node110Step2Chunk0_1_checked, root7Node110Step2Chunk0_2_checked, root7Node110Step2Chunk0_3_checked, root7Node110Step2Chunk0_4_checked, root7Node110Step2Chunk0_5_checked, root7Node110Step2Chunk1_0_checked, root7Node110Step2Chunk1_1_checked, root7Node110Step2Chunk1_2_checked, root7Node110Step2Chunk1_3_checked, root7Node110Step2Chunk1_4_checked, root7Node110Step2Chunk1_5_checked, root7Node110Step2Chunk2_0_checked, root7Node110Step2Chunk2_1_checked, root7Node110Step2Chunk2_2_checked, root7Node110Step2Chunk2_3_checked, root7Node110Step2Chunk2_4_checked, root7Node110Step2Chunk2_5_checked, root7Node110Step2Chunk3_0_checked, root7Node110Step2Chunk3_1_checked, root7Node110Step2Chunk3_2_checked, root7Node110Step2Chunk3_3_checked, root7Node110Step2Chunk3_4_checked, root7Node110Step2Chunk3_5_checked, root7Node110Step2Chunk4_0_checked, root7Node110Step2Chunk4_1_checked, root7Node110Step2Chunk4_2_checked, root7Node110Step2Chunk4_3_checked, root7Node110Step2Chunk4_4_checked, root7Node110Step2Chunk4_5_checked, root7Node110Step2Chunk5_0_checked, root7Node110Step2Chunk5_1_checked, root7Node110Step2Chunk5_2_checked, root7Node110Step2Chunk5_3_checked, root7Node110Step2Chunk5_4_checked, root7Node110Step2Chunk5_5_checked, root7Node110Step2Chunk6_0_checked, root7Node110Step2Chunk6_1_checked, root7Node110Step2Chunk6_2_checked, root7Node110Step2Chunk6_3_checked, root7Node110Step2Chunk6_4_checked, root7Node110Step2Chunk6_5_checked, root7Node110Step2Chunk7_0_checked, root7Node110Step2Chunk7_1_checked, root7Node110Step2Chunk7_2_checked, root7Node110Step2Chunk7_3_checked, root7Node110Step2Chunk7_4_checked, root7Node110Step2Chunk7_5_checked, root7Node110Step2Chunk8_0_checked, root7Node110Step2Chunk8_1_checked, root7Node110Step2Chunk8_2_checked, root7Node110Step2Chunk8_3_checked, root7Node110Step2Chunk8_4_checked, root7Node110Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node110Step2_checked :
    checkReplacement table31 root7Node110Domains1 root7Node110Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node110Domains1 root7Node110Domains2
    root7Node110Domains1Fast root7Node110Domains2Fast
    root7Node110Domains1_fast_eq root7Node110Domains2_fast_eq
    root7Node110Step2Narrowing_checked (by decide)
def root7Node110Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,4),(8,2),(8,4)]
  | 1 => [(0,0),(1,3),(6,4),(8,0)]
  | 2 => [(1,2),(3,2),(5,2),(7,2),(7,3),(8,2)]
  | 3 => [(4,0),(4,2),(8,0)]
  | 4 => [(5,3),(7,3),(8,3)]
  | 5 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 6 => [(0,4),(7,1),(8,1)]
  | 7 => [(1,5),(5,4),(6,5),(7,5)]
  | 8 => [(0,3),(0,4),(6,1),(6,4)]
  | 9 => [(1,2),(5,1),(5,4)]
  | 10 => [(0,1),(1,4),(6,4),(7,4)]
  | 11 => [(0,5),(1,2),(6,2),(6,3)]
  | 12 => [(4,4),(7,2),(7,4),(8,4)]
  | 13 => [(5,0),(5,3),(7,0),(8,0),(8,3)]
  | 14 => [(4,3),(4,5),(7,3),(8,5)]
  | 15 => [(3,5),(4,2),(7,0)]
  | 16 => [(0,3),(4,3),(5,3),(8,3)]
  | 17 => [(4,1),(7,5),(8,5)]
  | 18 => [(0,2),(0,3),(1,0),(6,0)]
  | 19 => [(1,1),(7,1),(8,1)]
  | 20 => [(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 21 => [(4,4),(5,4),(7,4),(8,4)]
  | 22 => [(0,0),(1,4),(6,3),(6,4)]
  | 23 => [(0,5),(1,2),(7,2)]
  | 24 => [(2,4),(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2),(5,2),(8,2)]
  | 27 => [(5,0),(5,3),(8,0)]
  | 28 => [(4,5),(7,3),(8,3),(8,5)]
  | 29 => [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 30 => [(4,1),(4,3),(7,1),(8,1)]
  | 31 => [(0,2),(1,5),(7,5)]
  | 32 => [(0,3),(1,1),(6,0),(6,1)]
  | 33 => [(7,1),(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(3,4),(5,4)]
  | 37 => [(0,0),(1,4),(6,3),(6,4)]
  | 38 => [(0,5),(1,2),(7,2)]
  | 39 => [(4,4),(7,4),(8,4)]
  | 40 => [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(7,4),(8,0)]
  | 41 => [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => [(4,2),(7,0),(8,0),(8,2)]
  | 43 => [(5,0),(5,3),(8,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3),(4,3)]
  | 47 => [(0,2),(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(1,1),(6,0),(6,1)]
  | 49 => [(4,1),(7,1),(8,1)]
  | 50 => [(0,2),(1,5),(6,5),(7,5)]
  | 51 => [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => [(1,4),(3,4),(7,4),(8,4)]
  | 54 => [(0,0),(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(6,4),(7,4)]
  | 57 => [(0,5),(1,2),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,0),(4,2),(8,2)]
  | 59 => [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 60 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 61 => [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(7,1),(7,5),(8,1)]
  | 63 => [(0,2),(1,5),(6,0)]
  | 64 => [(1,1),(6,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(0,3),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(5,4),(6,5)]
  | 69 => [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 70 => [(0,0),(1,3),(3,3),(5,0),(5,3),(6,4),(7,3)]
  | 71 => [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 72 => [(4,0),(7,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 75 => [(3,0),(5,0),(5,3),(7,0)]
  | 76 => [(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 77 => [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0),(7,5)]
  | 78 => [(0,0),(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 79 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => [(0,1),(1,4),(6,4),(7,4)]
  | 81 => [(0,5),(1,2),(6,2),(6,3)]
  | 82 => [(4,4),(7,2),(7,4),(8,4)]
  | 83 => [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => [(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 86 => [(3,5),(4,1),(7,5),(8,5)]
  | 87 => [(0,2),(0,3),(1,0),(6,0)]
  | 88 => [(1,1),(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
def root7Node110Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(4,4),(7,4),(8,2),(8,4)]
  | 1 => some [(0,0),(1,3),(6,4),(8,0)]
  | 2 => some [(1,2),(3,2),(5,2),(7,2),(7,3),(8,2)]
  | 3 => some [(4,0),(4,2),(8,0)]
  | 4 => some [(5,3),(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 6 => some [(0,4),(7,1),(8,1)]
  | 7 => some [(1,5),(5,4),(6,5),(7,5)]
  | 8 => some [(0,3),(0,4),(6,1),(6,4)]
  | 9 => some [(1,2),(5,1),(5,4)]
  | 10 => some [(0,1),(1,4),(6,4),(7,4)]
  | 11 => some [(0,5),(1,2),(6,2),(6,3)]
  | 12 => some [(4,4),(7,2),(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(7,0),(8,0),(8,3)]
  | 14 => some [(4,3),(4,5),(7,3),(8,5)]
  | 15 => some [(3,5),(4,2),(7,0)]
  | 16 => some [(0,3),(4,3),(5,3),(8,3)]
  | 17 => some [(4,1),(7,5),(8,5)]
  | 18 => some [(0,2),(0,3),(1,0),(6,0)]
  | 19 => some [(1,1),(7,1),(8,1)]
  | 20 => some [(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 21 => some [(4,4),(5,4),(7,4),(8,4)]
  | 22 => some [(0,0),(1,4),(6,3),(6,4)]
  | 23 => some [(0,5),(1,2),(7,2)]
  | 24 => some [(2,4),(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2),(5,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,3),(8,5)]
  | 29 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 30 => some [(4,1),(4,3),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5),(7,5)]
  | 32 => some [(0,3),(1,1),(6,0),(6,1)]
  | 33 => some [(7,1),(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4),(5,4)]
  | 37 => some [(0,0),(1,4),(6,3),(6,4)]
  | 38 => some [(0,5),(1,2),(7,2)]
  | 39 => some [(4,4),(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(7,4),(8,0)]
  | 41 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(7,0),(8,0),(8,2)]
  | 43 => some [(5,0),(5,3),(8,3)]
  | 44 => some [(4,5),(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3)]
  | 47 => some [(0,2),(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,0),(6,1)]
  | 49 => some [(4,1),(7,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5),(7,5)]
  | 51 => some [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => some [(1,4),(3,4),(7,4),(8,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(8,2)]
  | 59 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 60 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(7,1),(7,5),(8,1)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(5,4),(6,5)]
  | 69 => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 70 => some [(0,0),(1,3),(3,3),(5,0),(5,3),(6,4),(7,3)]
  | 71 => some [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 72 => some [(4,0),(7,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0)]
  | 76 => some [(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 77 => some [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0),(7,5)]
  | 78 => some [(0,0),(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 79 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4),(7,4)]
  | 81 => some [(0,5),(1,2),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => some [(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(3,5),(4,1),(7,5),(8,5)]
  | 87 => some [(0,2),(0,3),(1,0),(6,0)]
  | 88 => some [(1,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
theorem root7Node110Domains3_fast_eq : root7Node110Domains3 = expandDomains root7Node110Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node110Domains3 v = expandDomains root7Node110Domains3Fast v from by decide) v
theorem root7Node110Step3Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq (by decide)
theorem root7Node110Step3Narrowing_checked :
    checkNarrowing table52 root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root7Node110Domains2 root7Node110Domains3 (by
      simp only [List.all_cons, List.all_nil, root7Node110Step3Chunk0_0_checked, root7Node110Step3Chunk0_1_checked, root7Node110Step3Chunk0_2_checked, root7Node110Step3Chunk0_3_checked, root7Node110Step3Chunk0_4_checked, root7Node110Step3Chunk0_5_checked, root7Node110Step3Chunk1_0_checked, root7Node110Step3Chunk1_1_checked, root7Node110Step3Chunk1_2_checked, root7Node110Step3Chunk1_3_checked, root7Node110Step3Chunk1_4_checked, root7Node110Step3Chunk1_5_checked, root7Node110Step3Chunk2_0_checked, root7Node110Step3Chunk2_1_checked, root7Node110Step3Chunk2_2_checked, root7Node110Step3Chunk2_3_checked, root7Node110Step3Chunk2_4_checked, root7Node110Step3Chunk2_5_checked, root7Node110Step3Chunk3_0_checked, root7Node110Step3Chunk3_1_checked, root7Node110Step3Chunk3_2_checked, root7Node110Step3Chunk3_3_checked, root7Node110Step3Chunk3_4_checked, root7Node110Step3Chunk3_5_checked, root7Node110Step3Chunk4_0_checked, root7Node110Step3Chunk4_1_checked, root7Node110Step3Chunk4_2_checked, root7Node110Step3Chunk4_3_checked, root7Node110Step3Chunk4_4_checked, root7Node110Step3Chunk4_5_checked, root7Node110Step3Chunk5_0_checked, root7Node110Step3Chunk5_1_checked, root7Node110Step3Chunk5_2_checked, root7Node110Step3Chunk5_3_checked, root7Node110Step3Chunk5_4_checked, root7Node110Step3Chunk5_5_checked, root7Node110Step3Chunk6_0_checked, root7Node110Step3Chunk6_1_checked, root7Node110Step3Chunk6_2_checked, root7Node110Step3Chunk6_3_checked, root7Node110Step3Chunk6_4_checked, root7Node110Step3Chunk6_5_checked, root7Node110Step3Chunk7_0_checked, root7Node110Step3Chunk7_1_checked, root7Node110Step3Chunk7_2_checked, root7Node110Step3Chunk7_3_checked, root7Node110Step3Chunk7_4_checked, root7Node110Step3Chunk7_5_checked, root7Node110Step3Chunk8_0_checked, root7Node110Step3Chunk8_1_checked, root7Node110Step3Chunk8_2_checked, root7Node110Step3Chunk8_3_checked, root7Node110Step3Chunk8_4_checked, root7Node110Step3Chunk8_5_checked, Bool.true_and])
theorem root7Node110Step3_checked :
    checkReplacement table52 root7Node110Domains2 root7Node110Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root7Node110Domains2 root7Node110Domains3
    root7Node110Domains2Fast root7Node110Domains3Fast
    root7Node110Domains2_fast_eq root7Node110Domains3_fast_eq
    root7Node110Step3Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
