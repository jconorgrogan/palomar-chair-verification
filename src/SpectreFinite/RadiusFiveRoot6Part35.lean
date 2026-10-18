module

public import SpectreFinite.RadiusFiveRoot6Part34
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable0
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node82Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(1,1),(6,1)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(7,0),(8,0)]
  | 22 => [(8,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(4,4),(5,4),(8,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0)]
  | 37 => [(7,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(4,3),(7,1)]
  | 41 => [(7,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(1,4),(6,4)]
  | 51 => [(1,3),(7,3)]
  | 52 => [(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(1,0)]
  | 59 => [(7,1)]
  | 60 => [(7,5)]
  | 61 => [(0,4),(6,2)]
  | 62 => [(5,4),(8,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(4,0)]
  | 69 => [(7,3)]
  | 70 => [(4,3),(7,1)]
  | 71 => [(7,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(5,1)]
  | 77 => [(0,1)]
  | 78 => [(1,3),(7,3)]
  | 79 => [(4,2)]
  | 80 => [(5,3)]
  | 81 => [(5,5),(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(0,4),(1,2),(6,2)]
  | 86 => [(1,4),(3,4),(7,4)]
  | 87 => [(0,5),(6,3)]
  | 88 => [(4,4),(7,2)]
  | 89 => [(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root6Node82Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(1,1),(6,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0),(8,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(4,4),(5,4),(8,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0)]
  | 37 => some [(7,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(4,3),(7,1)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(1,4),(6,4)]
  | 51 => some [(1,3),(7,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0)]
  | 59 => some [(7,1)]
  | 60 => some [(7,5)]
  | 61 => some [(0,4),(6,2)]
  | 62 => some [(5,4),(8,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0)]
  | 69 => some [(7,3)]
  | 70 => some [(4,3),(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1)]
  | 77 => some [(0,1)]
  | 78 => some [(1,3),(7,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(1,2),(6,2)]
  | 86 => some [(1,4),(3,4),(7,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root6Node82Domains3_fast_eq : root6Node82Domains3 = expandDomains root6Node82Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node82Domains3 v = expandDomains root6Node82Domains3Fast v from by decide) v
theorem root6Node82Step3Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq (by decide)
theorem root6Node82Step3Narrowing_checked :
    checkNarrowing table36 root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root6Node82Domains2 root6Node82Domains3 (by
      simp only [List.all_cons, List.all_nil, root6Node82Step3Chunk0_0_checked, root6Node82Step3Chunk0_1_checked, root6Node82Step3Chunk0_2_checked, root6Node82Step3Chunk0_3_checked, root6Node82Step3Chunk0_4_checked, root6Node82Step3Chunk0_5_checked, root6Node82Step3Chunk1_0_checked, root6Node82Step3Chunk1_1_checked, root6Node82Step3Chunk1_2_checked, root6Node82Step3Chunk1_3_checked, root6Node82Step3Chunk1_4_checked, root6Node82Step3Chunk1_5_checked, root6Node82Step3Chunk2_0_checked, root6Node82Step3Chunk2_1_checked, root6Node82Step3Chunk2_2_checked, root6Node82Step3Chunk2_3_checked, root6Node82Step3Chunk2_4_checked, root6Node82Step3Chunk2_5_checked, root6Node82Step3Chunk3_0_checked, root6Node82Step3Chunk3_1_checked, root6Node82Step3Chunk3_2_checked, root6Node82Step3Chunk3_3_checked, root6Node82Step3Chunk3_4_checked, root6Node82Step3Chunk3_5_checked, root6Node82Step3Chunk4_0_checked, root6Node82Step3Chunk4_1_checked, root6Node82Step3Chunk4_2_checked, root6Node82Step3Chunk4_3_checked, root6Node82Step3Chunk4_4_checked, root6Node82Step3Chunk4_5_checked, root6Node82Step3Chunk5_0_checked, root6Node82Step3Chunk5_1_checked, root6Node82Step3Chunk5_2_checked, root6Node82Step3Chunk5_3_checked, root6Node82Step3Chunk5_4_checked, root6Node82Step3Chunk5_5_checked, root6Node82Step3Chunk6_0_checked, root6Node82Step3Chunk6_1_checked, root6Node82Step3Chunk6_2_checked, root6Node82Step3Chunk6_3_checked, root6Node82Step3Chunk6_4_checked, root6Node82Step3Chunk6_5_checked, root6Node82Step3Chunk7_0_checked, root6Node82Step3Chunk7_1_checked, root6Node82Step3Chunk7_2_checked, root6Node82Step3Chunk7_3_checked, root6Node82Step3Chunk7_4_checked, root6Node82Step3Chunk7_5_checked, root6Node82Step3Chunk8_0_checked, root6Node82Step3Chunk8_1_checked, root6Node82Step3Chunk8_2_checked, root6Node82Step3Chunk8_3_checked, root6Node82Step3Chunk8_4_checked, root6Node82Step3Chunk8_5_checked, Bool.true_and])
theorem root6Node82Step3_checked :
    checkReplacement table36 root6Node82Domains2 root6Node82Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root6Node82Domains2 root6Node82Domains3
    root6Node82Domains2Fast root6Node82Domains3Fast
    root6Node82Domains2_fast_eq root6Node82Domains3_fast_eq
    root6Node82Step3Narrowing_checked (by decide)
def root6Node83Domains0 : Domains 91 State := restrict root6Node82Domains3 13 (1,1)
def root6Node83Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(1,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0),(8,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(4,4),(5,4),(8,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0)]
  | 37 => some [(7,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(4,3),(7,1)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(1,4),(6,4)]
  | 51 => some [(1,3),(7,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0)]
  | 59 => some [(7,1)]
  | 60 => some [(7,5)]
  | 61 => some [(0,4),(6,2)]
  | 62 => some [(5,4),(8,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0)]
  | 69 => some [(7,3)]
  | 70 => some [(4,3),(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1)]
  | 77 => some [(0,1)]
  | 78 => some [(1,3),(7,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(1,2),(6,2)]
  | 86 => some [(1,4),(3,4),(7,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root6Node83Domains0_fast_eq : root6Node83Domains0 = expandDomains root6Node83Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node83Domains0 v = expandDomains root6Node83Domains0Fast v from by decide) v
def root6Node83Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(1,1)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(8,0)]
  | 22 => [(8,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(5,4),(8,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0)]
  | 37 => [(7,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(4,3),(7,1)]
  | 41 => [(7,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(1,4),(6,4)]
  | 51 => [(1,3),(7,3)]
  | 52 => [(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(1,0)]
  | 59 => [(7,1)]
  | 60 => [(7,5)]
  | 61 => [(0,4),(6,2)]
  | 62 => [(5,4),(8,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(4,0)]
  | 69 => [(7,3)]
  | 70 => [(4,3),(7,1)]
  | 71 => [(7,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(5,1)]
  | 77 => [(0,1)]
  | 78 => [(1,3),(7,3)]
  | 79 => [(4,2)]
  | 80 => [(5,3)]
  | 81 => [(5,5),(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(0,4),(1,2),(6,2)]
  | 86 => [(1,4),(3,4),(7,4)]
  | 87 => [(0,5),(6,3)]
  | 88 => [(4,4),(7,2)]
  | 89 => [(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root6Node83Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(1,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(8,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(5,4),(8,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0)]
  | 37 => some [(7,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(4,3),(7,1)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(1,4),(6,4)]
  | 51 => some [(1,3),(7,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0)]
  | 59 => some [(7,1)]
  | 60 => some [(7,5)]
  | 61 => some [(0,4),(6,2)]
  | 62 => some [(5,4),(8,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0)]
  | 69 => some [(7,3)]
  | 70 => some [(4,3),(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1)]
  | 77 => some [(0,1)]
  | 78 => some [(1,3),(7,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(1,2),(6,2)]
  | 86 => some [(1,4),(3,4),(7,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root6Node83Domains1_fast_eq : root6Node83Domains1 = expandDomains root6Node83Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node83Domains1 v = expandDomains root6Node83Domains1Fast v from by decide) v
theorem root6Node83Step1Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq (by decide)
theorem root6Node83Step1Narrowing_checked :
    checkNarrowing table0 root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkNarrowing_flatten table0Scope [table0Rows0_0,table0Rows0_1,table0Rows0_2,table0Rows0_3,table0Rows0_4,table0Rows0_5,table0Rows1_0,table0Rows1_1,table0Rows1_2,table0Rows1_3,table0Rows1_4,table0Rows1_5,table0Rows2_0,table0Rows2_1,table0Rows2_2,table0Rows2_3,table0Rows2_4,table0Rows2_5,table0Rows3_0,table0Rows3_1,table0Rows3_2,table0Rows3_3,table0Rows3_4,table0Rows3_5,table0Rows4_0,table0Rows4_1,table0Rows4_2,table0Rows4_3,table0Rows4_4,table0Rows4_5,table0Rows5_0,table0Rows5_1,table0Rows5_2,table0Rows5_3,table0Rows5_4,table0Rows5_5,table0Rows6_0,table0Rows6_1,table0Rows6_2,table0Rows6_3,table0Rows6_4,table0Rows6_5,table0Rows7_0,table0Rows7_1,table0Rows7_2,table0Rows7_3,table0Rows7_4,table0Rows7_5,table0Rows8_0,table0Rows8_1,table0Rows8_2,table0Rows8_3,table0Rows8_4,table0Rows8_5]
    root6Node83Domains0 root6Node83Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node83Step1Chunk0_0_checked, root6Node83Step1Chunk0_1_checked, root6Node83Step1Chunk0_2_checked, root6Node83Step1Chunk0_3_checked, root6Node83Step1Chunk0_4_checked, root6Node83Step1Chunk0_5_checked, root6Node83Step1Chunk1_0_checked, root6Node83Step1Chunk1_1_checked, root6Node83Step1Chunk1_2_checked, root6Node83Step1Chunk1_3_checked, root6Node83Step1Chunk1_4_checked, root6Node83Step1Chunk1_5_checked, root6Node83Step1Chunk2_0_checked, root6Node83Step1Chunk2_1_checked, root6Node83Step1Chunk2_2_checked, root6Node83Step1Chunk2_3_checked, root6Node83Step1Chunk2_4_checked, root6Node83Step1Chunk2_5_checked, root6Node83Step1Chunk3_0_checked, root6Node83Step1Chunk3_1_checked, root6Node83Step1Chunk3_2_checked, root6Node83Step1Chunk3_3_checked, root6Node83Step1Chunk3_4_checked, root6Node83Step1Chunk3_5_checked, root6Node83Step1Chunk4_0_checked, root6Node83Step1Chunk4_1_checked, root6Node83Step1Chunk4_2_checked, root6Node83Step1Chunk4_3_checked, root6Node83Step1Chunk4_4_checked, root6Node83Step1Chunk4_5_checked, root6Node83Step1Chunk5_0_checked, root6Node83Step1Chunk5_1_checked, root6Node83Step1Chunk5_2_checked, root6Node83Step1Chunk5_3_checked, root6Node83Step1Chunk5_4_checked, root6Node83Step1Chunk5_5_checked, root6Node83Step1Chunk6_0_checked, root6Node83Step1Chunk6_1_checked, root6Node83Step1Chunk6_2_checked, root6Node83Step1Chunk6_3_checked, root6Node83Step1Chunk6_4_checked, root6Node83Step1Chunk6_5_checked, root6Node83Step1Chunk7_0_checked, root6Node83Step1Chunk7_1_checked, root6Node83Step1Chunk7_2_checked, root6Node83Step1Chunk7_3_checked, root6Node83Step1Chunk7_4_checked, root6Node83Step1Chunk7_5_checked, root6Node83Step1Chunk8_0_checked, root6Node83Step1Chunk8_1_checked, root6Node83Step1Chunk8_2_checked, root6Node83Step1Chunk8_3_checked, root6Node83Step1Chunk8_4_checked, root6Node83Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node83Step1_checked :
    checkReplacement table0 root6Node83Domains0 root6Node83Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node83Domains0 root6Node83Domains1
    root6Node83Domains0Fast root6Node83Domains1Fast
    root6Node83Domains0_fast_eq root6Node83Domains1_fast_eq
    root6Node83Step1Narrowing_checked (by decide)
def root6Node84Domains0 : Domains 91 State := restrict root6Node83Domains1 30 (5,4)
def root6Node84Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(1,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(8,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(5,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0)]
  | 37 => some [(7,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(4,3),(7,1)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(1,4),(6,4)]
  | 51 => some [(1,3),(7,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0)]
  | 59 => some [(7,1)]
  | 60 => some [(7,5)]
  | 61 => some [(0,4),(6,2)]
  | 62 => some [(5,4),(8,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0)]
  | 69 => some [(7,3)]
  | 70 => some [(4,3),(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1)]
  | 77 => some [(0,1)]
  | 78 => some [(1,3),(7,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(1,2),(6,2)]
  | 86 => some [(1,4),(3,4),(7,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root6Node84Domains0_fast_eq : root6Node84Domains0 = expandDomains root6Node84Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node84Domains0 v = expandDomains root6Node84Domains0Fast v from by decide) v
def root6Node84Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(1,1)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(8,0)]
  | 22 => [(8,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(5,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0)]
  | 37 => [(7,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(4,3)]
  | 41 => [(7,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(1,4),(6,4)]
  | 51 => [(1,3)]
  | 52 => [(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(1,0)]
  | 59 => [(7,1)]
  | 60 => [(7,5)]
  | 61 => [(0,4)]
  | 62 => [(5,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(4,0)]
  | 69 => [(7,3)]
  | 70 => [(4,3)]
  | 71 => [(7,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(5,1)]
  | 77 => [(0,1)]
  | 78 => [(1,3)]
  | 79 => [(4,2)]
  | 80 => [(5,3)]
  | 81 => [(5,5),(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(0,4)]
  | 86 => [(1,4),(3,4)]
  | 87 => [(0,5),(6,3)]
  | 88 => [(4,4),(7,2)]
  | 89 => [(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root6Node84Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(1,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(8,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(5,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0)]
  | 37 => some [(7,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(4,3)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(1,4),(6,4)]
  | 51 => some [(1,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0)]
  | 59 => some [(7,1)]
  | 60 => some [(7,5)]
  | 61 => some [(0,4)]
  | 62 => some [(5,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0)]
  | 69 => some [(7,3)]
  | 70 => some [(4,3)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1)]
  | 77 => some [(0,1)]
  | 78 => some [(1,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(1,4),(3,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root6Node84Domains1_fast_eq : root6Node84Domains1 = expandDomains root6Node84Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node84Domains1 v = expandDomains root6Node84Domains1Fast v from by decide) v
theorem root6Node84Step1Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq (by decide)
theorem root6Node84Step1Narrowing_checked :
    checkNarrowing table52 root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root6Node84Domains0 root6Node84Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node84Step1Chunk0_0_checked, root6Node84Step1Chunk0_1_checked, root6Node84Step1Chunk0_2_checked, root6Node84Step1Chunk0_3_checked, root6Node84Step1Chunk0_4_checked, root6Node84Step1Chunk0_5_checked, root6Node84Step1Chunk1_0_checked, root6Node84Step1Chunk1_1_checked, root6Node84Step1Chunk1_2_checked, root6Node84Step1Chunk1_3_checked, root6Node84Step1Chunk1_4_checked, root6Node84Step1Chunk1_5_checked, root6Node84Step1Chunk2_0_checked, root6Node84Step1Chunk2_1_checked, root6Node84Step1Chunk2_2_checked, root6Node84Step1Chunk2_3_checked, root6Node84Step1Chunk2_4_checked, root6Node84Step1Chunk2_5_checked, root6Node84Step1Chunk3_0_checked, root6Node84Step1Chunk3_1_checked, root6Node84Step1Chunk3_2_checked, root6Node84Step1Chunk3_3_checked, root6Node84Step1Chunk3_4_checked, root6Node84Step1Chunk3_5_checked, root6Node84Step1Chunk4_0_checked, root6Node84Step1Chunk4_1_checked, root6Node84Step1Chunk4_2_checked, root6Node84Step1Chunk4_3_checked, root6Node84Step1Chunk4_4_checked, root6Node84Step1Chunk4_5_checked, root6Node84Step1Chunk5_0_checked, root6Node84Step1Chunk5_1_checked, root6Node84Step1Chunk5_2_checked, root6Node84Step1Chunk5_3_checked, root6Node84Step1Chunk5_4_checked, root6Node84Step1Chunk5_5_checked, root6Node84Step1Chunk6_0_checked, root6Node84Step1Chunk6_1_checked, root6Node84Step1Chunk6_2_checked, root6Node84Step1Chunk6_3_checked, root6Node84Step1Chunk6_4_checked, root6Node84Step1Chunk6_5_checked, root6Node84Step1Chunk7_0_checked, root6Node84Step1Chunk7_1_checked, root6Node84Step1Chunk7_2_checked, root6Node84Step1Chunk7_3_checked, root6Node84Step1Chunk7_4_checked, root6Node84Step1Chunk7_5_checked, root6Node84Step1Chunk8_0_checked, root6Node84Step1Chunk8_1_checked, root6Node84Step1Chunk8_2_checked, root6Node84Step1Chunk8_3_checked, root6Node84Step1Chunk8_4_checked, root6Node84Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node84Step1_checked :
    checkReplacement table52 root6Node84Domains0 root6Node84Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node84Domains0 root6Node84Domains1
    root6Node84Domains0Fast root6Node84Domains1Fast
    root6Node84Domains0_fast_eq root6Node84Domains1_fast_eq
    root6Node84Step1Narrowing_checked (by decide)
def root6Node84Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(1,1)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(8,0)]
  | 22 => [(8,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(5,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0)]
  | 37 => [(7,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(4,3)]
  | 41 => [(7,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(1,4),(6,4)]
  | 51 => [(1,3)]
  | 52 => [(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(1,0)]
  | 59 => [(7,1)]
  | 60 => [(7,5)]
  | 61 => [(0,4)]
  | 62 => [(5,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(4,0)]
  | 69 => [(7,3)]
  | 70 => [(4,3)]
  | 71 => [(7,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(5,1)]
  | 77 => [(0,1)]
  | 78 => [(1,3)]
  | 79 => [(4,2)]
  | 80 => [(5,3)]
  | 81 => [(5,5),(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(0,4)]
  | 86 => [(1,4),(3,4)]
  | 87 => [(0,5),(6,3)]
  | 88 => [(4,4),(7,2)]
  | 89 => [(1,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root6Node84Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(1,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(8,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(5,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0)]
  | 37 => some [(7,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(4,3)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(1,4),(6,4)]
  | 51 => some [(1,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0)]
  | 59 => some [(7,1)]
  | 60 => some [(7,5)]
  | 61 => some [(0,4)]
  | 62 => some [(5,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0)]
  | 69 => some [(7,3)]
  | 70 => some [(4,3)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1)]
  | 77 => some [(0,1)]
  | 78 => some [(1,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(1,4),(3,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node84Domains2_fast_eq : root6Node84Domains2 = expandDomains root6Node84Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node84Domains2 v = expandDomains root6Node84Domains2Fast v from by decide) v
theorem root6Node84Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq (by decide)
theorem root6Node84Step2Narrowing_checked :
    checkNarrowing table56 root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root6Node84Domains1 root6Node84Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node84Step2Chunk0_0_checked, root6Node84Step2Chunk0_1_checked, root6Node84Step2Chunk0_2_checked, root6Node84Step2Chunk0_3_checked, root6Node84Step2Chunk0_4_checked, root6Node84Step2Chunk0_5_checked, root6Node84Step2Chunk1_0_checked, root6Node84Step2Chunk1_1_checked, root6Node84Step2Chunk1_2_checked, root6Node84Step2Chunk1_3_checked, root6Node84Step2Chunk1_4_checked, root6Node84Step2Chunk1_5_checked, root6Node84Step2Chunk2_0_checked, root6Node84Step2Chunk2_1_checked, root6Node84Step2Chunk2_2_checked, root6Node84Step2Chunk2_3_checked, root6Node84Step2Chunk2_4_checked, root6Node84Step2Chunk2_5_checked, root6Node84Step2Chunk3_0_checked, root6Node84Step2Chunk3_1_checked, root6Node84Step2Chunk3_2_checked, root6Node84Step2Chunk3_3_checked, root6Node84Step2Chunk3_4_checked, root6Node84Step2Chunk3_5_checked, root6Node84Step2Chunk4_0_checked, root6Node84Step2Chunk4_1_checked, root6Node84Step2Chunk4_2_checked, root6Node84Step2Chunk4_3_checked, root6Node84Step2Chunk4_4_checked, root6Node84Step2Chunk4_5_checked, root6Node84Step2Chunk5_0_checked, root6Node84Step2Chunk5_1_checked, root6Node84Step2Chunk5_2_checked, root6Node84Step2Chunk5_3_checked, root6Node84Step2Chunk5_4_checked, root6Node84Step2Chunk5_5_checked, root6Node84Step2Chunk6_0_checked, root6Node84Step2Chunk6_1_checked, root6Node84Step2Chunk6_2_checked, root6Node84Step2Chunk6_3_checked, root6Node84Step2Chunk6_4_checked, root6Node84Step2Chunk6_5_checked, root6Node84Step2Chunk7_0_checked, root6Node84Step2Chunk7_1_checked, root6Node84Step2Chunk7_2_checked, root6Node84Step2Chunk7_3_checked, root6Node84Step2Chunk7_4_checked, root6Node84Step2Chunk7_5_checked, root6Node84Step2Chunk8_0_checked, root6Node84Step2Chunk8_1_checked, root6Node84Step2Chunk8_2_checked, root6Node84Step2Chunk8_3_checked, root6Node84Step2Chunk8_4_checked, root6Node84Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node84Step2_checked :
    checkReplacement table56 root6Node84Domains1 root6Node84Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node84Domains1 root6Node84Domains2
    root6Node84Domains1Fast root6Node84Domains2Fast
    root6Node84Domains1_fast_eq root6Node84Domains2_fast_eq
    root6Node84Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
