module

public import SpectreFinite.RadiusFourRoot4Part15
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable18
public import SpectreFinite.RadiusFourTable31
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node44Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(0,5)]
  | 6 => [(2,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(6,0)]
  | 12 => [(3,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(8,2)]
  | 19 => [(5,0)]
  | 20 => [(4,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(8,1)]
  | 26 => [(1,2)]
  | 27 => [(8,4)]
  | 28 => [(0,0)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(5,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(3,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(7,1)]
  | 59 => [(1,5)]
  | _ => [(6,1)]
def root4Node44Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5)]
  | 6 => some [(2,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(8,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(3,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(7,1)]
  | 59 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node44Domains3_fast_eq : root4Node44Domains3 = expandDomains root4Node44Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node44Domains3 v = expandDomains root4Node44Domains3Fast v from by decide) v
theorem root4Node44Step3Chunk0_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_0⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk0_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_1⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk0_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_2⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk0_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_3⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk0_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_4⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk0_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_5⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk1_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_0⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk1_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_1⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk1_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_2⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk1_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_3⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk1_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_4⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk1_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_5⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk2_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_0⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk2_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_1⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk2_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_2⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk2_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_3⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk2_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_4⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk2_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_5⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk3_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_0⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk3_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_1⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk3_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_2⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk3_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_3⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk3_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_4⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk3_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_5⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk4_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_0⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk4_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_1⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk4_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_2⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk4_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_3⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk4_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_4⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk4_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_5⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk5_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_0⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk5_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_1⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk5_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_2⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk5_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_3⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk5_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_4⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk5_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_5⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk6_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_0⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk6_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_1⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk6_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_2⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk6_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_3⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk6_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_4⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk6_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_5⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk7_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_0⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk7_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_1⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk7_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_2⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk7_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_3⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk7_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_4⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk7_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_5⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk8_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_0⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk8_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_1⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk8_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_2⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk8_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_3⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk8_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_4⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3Chunk8_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_5⟩
      root4Node44Domains2 root4Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node44Domains2 root4Node44Domains3
    root4Node44Domains2Fast root4Node44Domains3Fast
    root4Node44Domains2_fast_eq root4Node44Domains3_fast_eq (by decide)
theorem root4Node44Step3_checked :
    checkReplacement table18 root4Node44Domains2 root4Node44Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node44Step3Chunk0_0_checked, root4Node44Step3Chunk0_1_checked, root4Node44Step3Chunk0_2_checked, root4Node44Step3Chunk0_3_checked, root4Node44Step3Chunk0_4_checked, root4Node44Step3Chunk0_5_checked, root4Node44Step3Chunk1_0_checked, root4Node44Step3Chunk1_1_checked, root4Node44Step3Chunk1_2_checked, root4Node44Step3Chunk1_3_checked, root4Node44Step3Chunk1_4_checked, root4Node44Step3Chunk1_5_checked, root4Node44Step3Chunk2_0_checked, root4Node44Step3Chunk2_1_checked, root4Node44Step3Chunk2_2_checked, root4Node44Step3Chunk2_3_checked, root4Node44Step3Chunk2_4_checked, root4Node44Step3Chunk2_5_checked, root4Node44Step3Chunk3_0_checked, root4Node44Step3Chunk3_1_checked, root4Node44Step3Chunk3_2_checked, root4Node44Step3Chunk3_3_checked, root4Node44Step3Chunk3_4_checked, root4Node44Step3Chunk3_5_checked, root4Node44Step3Chunk4_0_checked, root4Node44Step3Chunk4_1_checked, root4Node44Step3Chunk4_2_checked, root4Node44Step3Chunk4_3_checked, root4Node44Step3Chunk4_4_checked, root4Node44Step3Chunk4_5_checked, root4Node44Step3Chunk5_0_checked, root4Node44Step3Chunk5_1_checked, root4Node44Step3Chunk5_2_checked, root4Node44Step3Chunk5_3_checked, root4Node44Step3Chunk5_4_checked, root4Node44Step3Chunk5_5_checked, root4Node44Step3Chunk6_0_checked, root4Node44Step3Chunk6_1_checked, root4Node44Step3Chunk6_2_checked, root4Node44Step3Chunk6_3_checked, root4Node44Step3Chunk6_4_checked, root4Node44Step3Chunk6_5_checked, root4Node44Step3Chunk7_0_checked, root4Node44Step3Chunk7_1_checked, root4Node44Step3Chunk7_2_checked, root4Node44Step3Chunk7_3_checked, root4Node44Step3Chunk7_4_checked, root4Node44Step3Chunk7_5_checked, root4Node44Step3Chunk8_0_checked, root4Node44Step3Chunk8_1_checked, root4Node44Step3Chunk8_2_checked, root4Node44Step3Chunk8_3_checked, root4Node44Step3Chunk8_4_checked, root4Node44Step3Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node44Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node44Domains3 (.output 21) = true := by decide
def root4Node45Domains0 : Domains 61 State := restrict root4Node43Domains2 10 (8,3)
def root4Node45Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5)]
  | 6 => some [(2,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(8,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(1,2),(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,5)]
  | 35 => some [(7,1),(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3),(6,4)]
  | 43 => some [(4,5),(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node45Domains0_fast_eq : root4Node45Domains0 = expandDomains root4Node45Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node45Domains0 v = expandDomains root4Node45Domains0Fast v from by decide) v
def root4Node45Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(0,5)]
  | 6 => [(2,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(6,0)]
  | 12 => [(3,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(8,2)]
  | 19 => [(5,0)]
  | 20 => [(4,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(1,2),(6,2)]
  | 27 => [(8,4)]
  | 28 => [(0,0)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
  | 33 => [(5,0),(8,0)]
  | 34 => [(4,5),(7,3)]
  | 35 => [(7,1),(8,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(4,5),(5,5),(8,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(4,4),(7,2)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(1,3),(6,3)]
  | 53 => [(7,2),(8,2)]
  | 54 => [(4,0),(5,0),(8,0)]
  | 55 => [(4,5),(7,3)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root4Node45Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5)]
  | 6 => some [(2,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(8,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,2),(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0),(8,0)]
  | 34 => some [(4,5),(7,3)]
  | 35 => some [(7,1),(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5),(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(1,3),(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node45Domains1_fast_eq : root4Node45Domains1 = expandDomains root4Node45Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node45Domains1 v = expandDomains root4Node45Domains1Fast v from by decide) v
theorem root4Node45Step1Chunk0_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk0_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk0_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk0_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk0_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk0_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk1_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk1_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk1_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk1_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk1_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk1_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk2_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk2_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk2_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk2_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk2_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk2_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk3_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk3_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk3_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk3_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk3_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk3_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk4_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk4_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk4_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk4_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk4_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk4_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk5_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk5_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk5_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk5_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk5_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk5_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk6_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk6_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk6_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk6_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk6_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk6_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk7_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk7_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk7_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk7_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk7_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk7_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk8_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_0⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk8_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_1⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk8_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_2⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk8_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_3⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk8_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_4⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1Chunk8_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_5⟩
      root4Node45Domains0 root4Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains0 root4Node45Domains1
    root4Node45Domains0Fast root4Node45Domains1Fast
    root4Node45Domains0_fast_eq root4Node45Domains1_fast_eq (by decide)
theorem root4Node45Step1_checked :
    checkReplacement table31 root4Node45Domains0 root4Node45Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node45Step1Chunk0_0_checked, root4Node45Step1Chunk0_1_checked, root4Node45Step1Chunk0_2_checked, root4Node45Step1Chunk0_3_checked, root4Node45Step1Chunk0_4_checked, root4Node45Step1Chunk0_5_checked, root4Node45Step1Chunk1_0_checked, root4Node45Step1Chunk1_1_checked, root4Node45Step1Chunk1_2_checked, root4Node45Step1Chunk1_3_checked, root4Node45Step1Chunk1_4_checked, root4Node45Step1Chunk1_5_checked, root4Node45Step1Chunk2_0_checked, root4Node45Step1Chunk2_1_checked, root4Node45Step1Chunk2_2_checked, root4Node45Step1Chunk2_3_checked, root4Node45Step1Chunk2_4_checked, root4Node45Step1Chunk2_5_checked, root4Node45Step1Chunk3_0_checked, root4Node45Step1Chunk3_1_checked, root4Node45Step1Chunk3_2_checked, root4Node45Step1Chunk3_3_checked, root4Node45Step1Chunk3_4_checked, root4Node45Step1Chunk3_5_checked, root4Node45Step1Chunk4_0_checked, root4Node45Step1Chunk4_1_checked, root4Node45Step1Chunk4_2_checked, root4Node45Step1Chunk4_3_checked, root4Node45Step1Chunk4_4_checked, root4Node45Step1Chunk4_5_checked, root4Node45Step1Chunk5_0_checked, root4Node45Step1Chunk5_1_checked, root4Node45Step1Chunk5_2_checked, root4Node45Step1Chunk5_3_checked, root4Node45Step1Chunk5_4_checked, root4Node45Step1Chunk5_5_checked, root4Node45Step1Chunk6_0_checked, root4Node45Step1Chunk6_1_checked, root4Node45Step1Chunk6_2_checked, root4Node45Step1Chunk6_3_checked, root4Node45Step1Chunk6_4_checked, root4Node45Step1Chunk6_5_checked, root4Node45Step1Chunk7_0_checked, root4Node45Step1Chunk7_1_checked, root4Node45Step1Chunk7_2_checked, root4Node45Step1Chunk7_3_checked, root4Node45Step1Chunk7_4_checked, root4Node45Step1Chunk7_5_checked, root4Node45Step1Chunk8_0_checked, root4Node45Step1Chunk8_1_checked, root4Node45Step1Chunk8_2_checked, root4Node45Step1Chunk8_3_checked, root4Node45Step1Chunk8_4_checked, root4Node45Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node45Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(0,5)]
  | 6 => [(2,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(6,0)]
  | 12 => [(3,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(8,2)]
  | 19 => [(5,0)]
  | 20 => [(4,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(1,2),(6,2)]
  | 27 => [(8,4)]
  | 28 => [(0,0)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
  | 33 => [(5,0),(8,0)]
  | 34 => [(4,5),(7,3)]
  | 35 => [(7,1),(8,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(4,5),(8,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3),(6,3)]
  | 53 => [(7,2),(8,2)]
  | 54 => [(4,0),(5,0),(8,0)]
  | 55 => [(4,5),(7,3)]
  | 56 => [(4,1),(8,1)]
  | 57 => [(0,2),(6,5)]
  | 58 => [(0,4),(1,1)]
  | 59 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,4)]
def root4Node45Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5)]
  | 6 => some [(2,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(8,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,2),(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0),(8,0)]
  | 34 => some [(4,5),(7,3)]
  | 35 => some [(7,1),(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3),(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,4)]
theorem root4Node45Domains2_fast_eq : root4Node45Domains2 = expandDomains root4Node45Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node45Domains2 v = expandDomains root4Node45Domains2Fast v from by decide) v
theorem root4Node45Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root4Node45Domains1 root4Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node45Domains1 root4Node45Domains2
    root4Node45Domains1Fast root4Node45Domains2Fast
    root4Node45Domains1_fast_eq root4Node45Domains2_fast_eq (by decide)
theorem root4Node45Step2_checked :
    checkReplacement table46 root4Node45Domains1 root4Node45Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node45Step2Chunk0_0_checked, root4Node45Step2Chunk0_1_checked, root4Node45Step2Chunk0_2_checked, root4Node45Step2Chunk0_3_checked, root4Node45Step2Chunk0_4_checked, root4Node45Step2Chunk0_5_checked, root4Node45Step2Chunk1_0_checked, root4Node45Step2Chunk1_1_checked, root4Node45Step2Chunk1_2_checked, root4Node45Step2Chunk1_3_checked, root4Node45Step2Chunk1_4_checked, root4Node45Step2Chunk1_5_checked, root4Node45Step2Chunk2_0_checked, root4Node45Step2Chunk2_1_checked, root4Node45Step2Chunk2_2_checked, root4Node45Step2Chunk2_3_checked, root4Node45Step2Chunk2_4_checked, root4Node45Step2Chunk2_5_checked, root4Node45Step2Chunk3_0_checked, root4Node45Step2Chunk3_1_checked, root4Node45Step2Chunk3_2_checked, root4Node45Step2Chunk3_3_checked, root4Node45Step2Chunk3_4_checked, root4Node45Step2Chunk3_5_checked, root4Node45Step2Chunk4_0_checked, root4Node45Step2Chunk4_1_checked, root4Node45Step2Chunk4_2_checked, root4Node45Step2Chunk4_3_checked, root4Node45Step2Chunk4_4_checked, root4Node45Step2Chunk4_5_checked, root4Node45Step2Chunk5_0_checked, root4Node45Step2Chunk5_1_checked, root4Node45Step2Chunk5_2_checked, root4Node45Step2Chunk5_3_checked, root4Node45Step2Chunk5_4_checked, root4Node45Step2Chunk5_5_checked, root4Node45Step2Chunk6_0_checked, root4Node45Step2Chunk6_1_checked, root4Node45Step2Chunk6_2_checked, root4Node45Step2Chunk6_3_checked, root4Node45Step2Chunk6_4_checked, root4Node45Step2Chunk6_5_checked, root4Node45Step2Chunk7_0_checked, root4Node45Step2Chunk7_1_checked, root4Node45Step2Chunk7_2_checked, root4Node45Step2Chunk7_3_checked, root4Node45Step2Chunk7_4_checked, root4Node45Step2Chunk7_5_checked, root4Node45Step2Chunk8_0_checked, root4Node45Step2Chunk8_1_checked, root4Node45Step2Chunk8_2_checked, root4Node45Step2Chunk8_3_checked, root4Node45Step2Chunk8_4_checked, root4Node45Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node46Domains0 : Domains 61 State := restrict root4Node45Domains2 26 (1,2)
def root4Node46Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5)]
  | 6 => some [(2,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(8,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0),(8,0)]
  | 34 => some [(4,5),(7,3)]
  | 35 => some [(7,1),(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3),(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,4)]
theorem root4Node46Domains0_fast_eq : root4Node46Domains0 = expandDomains root4Node46Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node46Domains0 v = expandDomains root4Node46Domains0Fast v from by decide) v
def root4Node46Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(0,5)]
  | 6 => [(2,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(6,0)]
  | 12 => [(3,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(8,2)]
  | 19 => [(5,0)]
  | 20 => [(4,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(1,2)]
  | 27 => [(8,4)]
  | 28 => [(0,0)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
  | 33 => [(5,0),(8,0)]
  | 34 => [(4,5),(7,3)]
  | 35 => [(8,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(8,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3),(6,3)]
  | 53 => [(7,2),(8,2)]
  | 54 => [(4,0),(5,0),(8,0)]
  | 55 => [(4,5),(7,3)]
  | 56 => [(4,1),(8,1)]
  | 57 => [(0,2),(6,5)]
  | 58 => [(0,4),(1,1)]
  | 59 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,4)]
def root4Node46Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5)]
  | 6 => some [(2,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(8,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0),(8,0)]
  | 34 => some [(4,5),(7,3)]
  | 35 => some [(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3),(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,4)]
theorem root4Node46Domains1_fast_eq : root4Node46Domains1 = expandDomains root4Node46Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node46Domains1 v = expandDomains root4Node46Domains1Fast v from by decide) v
theorem root4Node46Step1Chunk0_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk0_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk0_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk0_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk0_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk0_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk1_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk1_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk1_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk1_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk1_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk1_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk2_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk2_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk2_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk2_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk2_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk2_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk3_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk3_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk3_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk3_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk3_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk3_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk4_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk4_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk4_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk4_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk4_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk4_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk5_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk5_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk5_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk5_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk5_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk5_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk6_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk6_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk6_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk6_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk6_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk6_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk7_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk7_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk7_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk7_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk7_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk7_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk8_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_0⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk8_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_1⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk8_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_2⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk8_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_3⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk8_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_4⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1Chunk8_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_5⟩
      root4Node46Domains0 root4Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains0 root4Node46Domains1
    root4Node46Domains0Fast root4Node46Domains1Fast
    root4Node46Domains0_fast_eq root4Node46Domains1_fast_eq (by decide)
theorem root4Node46Step1_checked :
    checkReplacement table18 root4Node46Domains0 root4Node46Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node46Step1Chunk0_0_checked, root4Node46Step1Chunk0_1_checked, root4Node46Step1Chunk0_2_checked, root4Node46Step1Chunk0_3_checked, root4Node46Step1Chunk0_4_checked, root4Node46Step1Chunk0_5_checked, root4Node46Step1Chunk1_0_checked, root4Node46Step1Chunk1_1_checked, root4Node46Step1Chunk1_2_checked, root4Node46Step1Chunk1_3_checked, root4Node46Step1Chunk1_4_checked, root4Node46Step1Chunk1_5_checked, root4Node46Step1Chunk2_0_checked, root4Node46Step1Chunk2_1_checked, root4Node46Step1Chunk2_2_checked, root4Node46Step1Chunk2_3_checked, root4Node46Step1Chunk2_4_checked, root4Node46Step1Chunk2_5_checked, root4Node46Step1Chunk3_0_checked, root4Node46Step1Chunk3_1_checked, root4Node46Step1Chunk3_2_checked, root4Node46Step1Chunk3_3_checked, root4Node46Step1Chunk3_4_checked, root4Node46Step1Chunk3_5_checked, root4Node46Step1Chunk4_0_checked, root4Node46Step1Chunk4_1_checked, root4Node46Step1Chunk4_2_checked, root4Node46Step1Chunk4_3_checked, root4Node46Step1Chunk4_4_checked, root4Node46Step1Chunk4_5_checked, root4Node46Step1Chunk5_0_checked, root4Node46Step1Chunk5_1_checked, root4Node46Step1Chunk5_2_checked, root4Node46Step1Chunk5_3_checked, root4Node46Step1Chunk5_4_checked, root4Node46Step1Chunk5_5_checked, root4Node46Step1Chunk6_0_checked, root4Node46Step1Chunk6_1_checked, root4Node46Step1Chunk6_2_checked, root4Node46Step1Chunk6_3_checked, root4Node46Step1Chunk6_4_checked, root4Node46Step1Chunk6_5_checked, root4Node46Step1Chunk7_0_checked, root4Node46Step1Chunk7_1_checked, root4Node46Step1Chunk7_2_checked, root4Node46Step1Chunk7_3_checked, root4Node46Step1Chunk7_4_checked, root4Node46Step1Chunk7_5_checked, root4Node46Step1Chunk8_0_checked, root4Node46Step1Chunk8_1_checked, root4Node46Step1Chunk8_2_checked, root4Node46Step1Chunk8_3_checked, root4Node46Step1Chunk8_4_checked, root4Node46Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node47Domains0 : Domains 61 State := restrict root4Node46Domains1 33 (5,0)
def root4Node47Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5)]
  | 6 => some [(2,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(8,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5),(7,3)]
  | 35 => some [(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3),(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,4)]
theorem root4Node47Domains0_fast_eq : root4Node47Domains0 = expandDomains root4Node47Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node47Domains0 v = expandDomains root4Node47Domains0Fast v from by decide) v
def root4Node47Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(0,5)]
  | 6 => [(2,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(6,0)]
  | 12 => [(3,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(8,2)]
  | 19 => [(5,0)]
  | 20 => [(4,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(1,2)]
  | 27 => [(8,4)]
  | 28 => [(0,0)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5),(7,3)]
  | 35 => [(8,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(8,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(4,1),(8,1)]
  | 57 => [(6,5)]
  | 58 => [(0,4)]
  | 59 => [(5,4)]
  | _ => [(0,0)]
def root4Node47Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5)]
  | 6 => some [(2,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,0)]
  | 12 => some [(3,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(8,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5),(7,3)]
  | 35 => some [(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(5,4)]
  | _ => some [(0,0)]
theorem root4Node47Domains1_fast_eq : root4Node47Domains1 = expandDomains root4Node47Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node47Domains1 v = expandDomains root4Node47Domains1Fast v from by decide) v
theorem root4Node47Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1_checked :
    checkReplacement table39 root4Node47Domains0 root4Node47Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node47Step1Chunk0_0_checked, root4Node47Step1Chunk0_1_checked, root4Node47Step1Chunk0_2_checked, root4Node47Step1Chunk0_3_checked, root4Node47Step1Chunk0_4_checked, root4Node47Step1Chunk0_5_checked, root4Node47Step1Chunk1_0_checked, root4Node47Step1Chunk1_1_checked, root4Node47Step1Chunk1_2_checked, root4Node47Step1Chunk1_3_checked, root4Node47Step1Chunk1_4_checked, root4Node47Step1Chunk1_5_checked, root4Node47Step1Chunk2_0_checked, root4Node47Step1Chunk2_1_checked, root4Node47Step1Chunk2_2_checked, root4Node47Step1Chunk2_3_checked, root4Node47Step1Chunk2_4_checked, root4Node47Step1Chunk2_5_checked, root4Node47Step1Chunk3_0_checked, root4Node47Step1Chunk3_1_checked, root4Node47Step1Chunk3_2_checked, root4Node47Step1Chunk3_3_checked, root4Node47Step1Chunk3_4_checked, root4Node47Step1Chunk3_5_checked, root4Node47Step1Chunk4_0_checked, root4Node47Step1Chunk4_1_checked, root4Node47Step1Chunk4_2_checked, root4Node47Step1Chunk4_3_checked, root4Node47Step1Chunk4_4_checked, root4Node47Step1Chunk4_5_checked, root4Node47Step1Chunk5_0_checked, root4Node47Step1Chunk5_1_checked, root4Node47Step1Chunk5_2_checked, root4Node47Step1Chunk5_3_checked, root4Node47Step1Chunk5_4_checked, root4Node47Step1Chunk5_5_checked, root4Node47Step1Chunk6_0_checked, root4Node47Step1Chunk6_1_checked, root4Node47Step1Chunk6_2_checked, root4Node47Step1Chunk6_3_checked, root4Node47Step1Chunk6_4_checked, root4Node47Step1Chunk6_5_checked, root4Node47Step1Chunk7_0_checked, root4Node47Step1Chunk7_1_checked, root4Node47Step1Chunk7_2_checked, root4Node47Step1Chunk7_3_checked, root4Node47Step1Chunk7_4_checked, root4Node47Step1Chunk7_5_checked, root4Node47Step1Chunk8_0_checked, root4Node47Step1Chunk8_1_checked, root4Node47Step1Chunk8_2_checked, root4Node47Step1Chunk8_3_checked, root4Node47Step1Chunk8_4_checked, root4Node47Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
