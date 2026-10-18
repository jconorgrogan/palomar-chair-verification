module

public import SpectreFinite.RadiusFourRoot0Part17
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node52Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5)]
  | 3 => [(6,1)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,0)]
  | 9 => [(7,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(3,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(5,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(4,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(5,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5)]
  | 49 => [(1,0)]
  | 50 => [(1,4)]
  | 51 => [(0,5)]
  | 52 => [(4,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(6,0)]
  | 57 => [(7,1)]
  | 58 => [(7,5)]
  | 59 => [(6,0)]
  | _ => [(7,1)]
def root0Node52Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,0)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(3,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(4,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(5,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5)]
  | 49 => some [(1,0)]
  | 50 => some [(1,4)]
  | 51 => some [(0,5)]
  | 52 => some [(4,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(6,0)]
  | 57 => some [(7,1)]
  | 58 => some [(7,5)]
  | 59 => some [(6,0)]
  | _ => some [(7,1)]
theorem root0Node52Domains2_fast_eq : root0Node52Domains2 = expandDomains root0Node52Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node52Domains2 v = expandDomains root0Node52Domains2Fast v from by decide) v
theorem root0Node52Step2Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root0Node52Domains1 root0Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node52Domains1 root0Node52Domains2
    root0Node52Domains1Fast root0Node52Domains2Fast
    root0Node52Domains1_fast_eq root0Node52Domains2_fast_eq (by decide)
theorem root0Node52Step2_checked :
    checkReplacement table36 root0Node52Domains1 root0Node52Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node52Step2Chunk0_0_checked, root0Node52Step2Chunk0_1_checked, root0Node52Step2Chunk0_2_checked, root0Node52Step2Chunk0_3_checked, root0Node52Step2Chunk0_4_checked, root0Node52Step2Chunk0_5_checked, root0Node52Step2Chunk1_0_checked, root0Node52Step2Chunk1_1_checked, root0Node52Step2Chunk1_2_checked, root0Node52Step2Chunk1_3_checked, root0Node52Step2Chunk1_4_checked, root0Node52Step2Chunk1_5_checked, root0Node52Step2Chunk2_0_checked, root0Node52Step2Chunk2_1_checked, root0Node52Step2Chunk2_2_checked, root0Node52Step2Chunk2_3_checked, root0Node52Step2Chunk2_4_checked, root0Node52Step2Chunk2_5_checked, root0Node52Step2Chunk3_0_checked, root0Node52Step2Chunk3_1_checked, root0Node52Step2Chunk3_2_checked, root0Node52Step2Chunk3_3_checked, root0Node52Step2Chunk3_4_checked, root0Node52Step2Chunk3_5_checked, root0Node52Step2Chunk4_0_checked, root0Node52Step2Chunk4_1_checked, root0Node52Step2Chunk4_2_checked, root0Node52Step2Chunk4_3_checked, root0Node52Step2Chunk4_4_checked, root0Node52Step2Chunk4_5_checked, root0Node52Step2Chunk5_0_checked, root0Node52Step2Chunk5_1_checked, root0Node52Step2Chunk5_2_checked, root0Node52Step2Chunk5_3_checked, root0Node52Step2Chunk5_4_checked, root0Node52Step2Chunk5_5_checked, root0Node52Step2Chunk6_0_checked, root0Node52Step2Chunk6_1_checked, root0Node52Step2Chunk6_2_checked, root0Node52Step2Chunk6_3_checked, root0Node52Step2Chunk6_4_checked, root0Node52Step2Chunk6_5_checked, root0Node52Step2Chunk7_0_checked, root0Node52Step2Chunk7_1_checked, root0Node52Step2Chunk7_2_checked, root0Node52Step2Chunk7_3_checked, root0Node52Step2Chunk7_4_checked, root0Node52Step2Chunk7_5_checked, root0Node52Step2Chunk8_0_checked, root0Node52Step2Chunk8_1_checked, root0Node52Step2Chunk8_2_checked, root0Node52Step2Chunk8_3_checked, root0Node52Step2Chunk8_4_checked, root0Node52Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node52Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node52Domains2 (.output 24) = true := by decide
def root0Node53Domains0 : Domains 61 State := restrict root0Node51Domains2 34 (8,2)
def root0Node53Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,0)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(3,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(1,4),(3,4)]
  | 51 => some [(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2),(6,0)]
  | 57 => some [(1,1),(7,1)]
  | 58 => some [(4,1),(7,5)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node53Domains0_fast_eq : root0Node53Domains0 = expandDomains root0Node53Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node53Domains0 v = expandDomains root0Node53Domains0Fast v from by decide) v
def root0Node53Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5)]
  | 3 => [(6,1)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,0)]
  | 9 => [(7,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(3,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(5,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(1,4),(3,4)]
  | 51 => [(0,5),(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(0,2),(6,0)]
  | 57 => [(1,1),(7,1)]
  | 58 => [(4,1)]
  | 59 => [(0,2)]
  | _ => [(1,1)]
def root0Node53Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,0)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(3,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(1,4),(3,4)]
  | 51 => some [(0,5),(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(0,2),(6,0)]
  | 57 => some [(1,1),(7,1)]
  | 58 => some [(4,1)]
  | 59 => some [(0,2)]
  | _ => some [(1,1)]
theorem root0Node53Domains1_fast_eq : root0Node53Domains1 = expandDomains root0Node53Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node53Domains1 v = expandDomains root0Node53Domains1Fast v from by decide) v
theorem root0Node53Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root0Node53Domains0 root0Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains0 root0Node53Domains1
    root0Node53Domains0Fast root0Node53Domains1Fast
    root0Node53Domains0_fast_eq root0Node53Domains1_fast_eq (by decide)
theorem root0Node53Step1_checked :
    checkReplacement table40 root0Node53Domains0 root0Node53Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node53Step1Chunk0_0_checked, root0Node53Step1Chunk0_1_checked, root0Node53Step1Chunk0_2_checked, root0Node53Step1Chunk0_3_checked, root0Node53Step1Chunk0_4_checked, root0Node53Step1Chunk0_5_checked, root0Node53Step1Chunk1_0_checked, root0Node53Step1Chunk1_1_checked, root0Node53Step1Chunk1_2_checked, root0Node53Step1Chunk1_3_checked, root0Node53Step1Chunk1_4_checked, root0Node53Step1Chunk1_5_checked, root0Node53Step1Chunk2_0_checked, root0Node53Step1Chunk2_1_checked, root0Node53Step1Chunk2_2_checked, root0Node53Step1Chunk2_3_checked, root0Node53Step1Chunk2_4_checked, root0Node53Step1Chunk2_5_checked, root0Node53Step1Chunk3_0_checked, root0Node53Step1Chunk3_1_checked, root0Node53Step1Chunk3_2_checked, root0Node53Step1Chunk3_3_checked, root0Node53Step1Chunk3_4_checked, root0Node53Step1Chunk3_5_checked, root0Node53Step1Chunk4_0_checked, root0Node53Step1Chunk4_1_checked, root0Node53Step1Chunk4_2_checked, root0Node53Step1Chunk4_3_checked, root0Node53Step1Chunk4_4_checked, root0Node53Step1Chunk4_5_checked, root0Node53Step1Chunk5_0_checked, root0Node53Step1Chunk5_1_checked, root0Node53Step1Chunk5_2_checked, root0Node53Step1Chunk5_3_checked, root0Node53Step1Chunk5_4_checked, root0Node53Step1Chunk5_5_checked, root0Node53Step1Chunk6_0_checked, root0Node53Step1Chunk6_1_checked, root0Node53Step1Chunk6_2_checked, root0Node53Step1Chunk6_3_checked, root0Node53Step1Chunk6_4_checked, root0Node53Step1Chunk6_5_checked, root0Node53Step1Chunk7_0_checked, root0Node53Step1Chunk7_1_checked, root0Node53Step1Chunk7_2_checked, root0Node53Step1Chunk7_3_checked, root0Node53Step1Chunk7_4_checked, root0Node53Step1Chunk7_5_checked, root0Node53Step1Chunk8_0_checked, root0Node53Step1Chunk8_1_checked, root0Node53Step1Chunk8_2_checked, root0Node53Step1Chunk8_3_checked, root0Node53Step1Chunk8_4_checked, root0Node53Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node53Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5)]
  | 3 => [(6,1)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,0)]
  | 9 => [(7,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(3,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(5,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(3,4)]
  | 51 => [(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(0,2)]
  | 57 => [(1,1)]
  | 58 => [(4,1)]
  | 59 => [(0,2)]
  | _ => [(1,1)]
def root0Node53Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,0)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(3,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(3,4)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(0,2)]
  | 57 => some [(1,1)]
  | 58 => some [(4,1)]
  | 59 => some [(0,2)]
  | _ => some [(1,1)]
theorem root0Node53Domains2_fast_eq : root0Node53Domains2 = expandDomains root0Node53Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node53Domains2 v = expandDomains root0Node53Domains2Fast v from by decide) v
theorem root0Node53Step2Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root0Node53Domains1 root0Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node53Domains1 root0Node53Domains2
    root0Node53Domains1Fast root0Node53Domains2Fast
    root0Node53Domains1_fast_eq root0Node53Domains2_fast_eq (by decide)
theorem root0Node53Step2_checked :
    checkReplacement table36 root0Node53Domains1 root0Node53Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node53Step2Chunk0_0_checked, root0Node53Step2Chunk0_1_checked, root0Node53Step2Chunk0_2_checked, root0Node53Step2Chunk0_3_checked, root0Node53Step2Chunk0_4_checked, root0Node53Step2Chunk0_5_checked, root0Node53Step2Chunk1_0_checked, root0Node53Step2Chunk1_1_checked, root0Node53Step2Chunk1_2_checked, root0Node53Step2Chunk1_3_checked, root0Node53Step2Chunk1_4_checked, root0Node53Step2Chunk1_5_checked, root0Node53Step2Chunk2_0_checked, root0Node53Step2Chunk2_1_checked, root0Node53Step2Chunk2_2_checked, root0Node53Step2Chunk2_3_checked, root0Node53Step2Chunk2_4_checked, root0Node53Step2Chunk2_5_checked, root0Node53Step2Chunk3_0_checked, root0Node53Step2Chunk3_1_checked, root0Node53Step2Chunk3_2_checked, root0Node53Step2Chunk3_3_checked, root0Node53Step2Chunk3_4_checked, root0Node53Step2Chunk3_5_checked, root0Node53Step2Chunk4_0_checked, root0Node53Step2Chunk4_1_checked, root0Node53Step2Chunk4_2_checked, root0Node53Step2Chunk4_3_checked, root0Node53Step2Chunk4_4_checked, root0Node53Step2Chunk4_5_checked, root0Node53Step2Chunk5_0_checked, root0Node53Step2Chunk5_1_checked, root0Node53Step2Chunk5_2_checked, root0Node53Step2Chunk5_3_checked, root0Node53Step2Chunk5_4_checked, root0Node53Step2Chunk5_5_checked, root0Node53Step2Chunk6_0_checked, root0Node53Step2Chunk6_1_checked, root0Node53Step2Chunk6_2_checked, root0Node53Step2Chunk6_3_checked, root0Node53Step2Chunk6_4_checked, root0Node53Step2Chunk6_5_checked, root0Node53Step2Chunk7_0_checked, root0Node53Step2Chunk7_1_checked, root0Node53Step2Chunk7_2_checked, root0Node53Step2Chunk7_3_checked, root0Node53Step2Chunk7_4_checked, root0Node53Step2Chunk7_5_checked, root0Node53Step2Chunk8_0_checked, root0Node53Step2Chunk8_1_checked, root0Node53Step2Chunk8_2_checked, root0Node53Step2Chunk8_3_checked, root0Node53Step2Chunk8_4_checked, root0Node53Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node53Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node53Domains2 (.output 25) = true := by decide
def root0Node54Domains0 : Domains 61 State := restrict root0Node50Domains1 26 (8,4)
def root0Node54Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,0)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(3,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(1,4),(3,4),(7,4)]
  | 51 => some [(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,2),(6,0)]
  | 57 => some [(1,1),(7,1)]
  | 58 => some [(4,1),(7,5),(8,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node54Domains0_fast_eq : root0Node54Domains0 = expandDomains root0Node54Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node54Domains0 v = expandDomains root0Node54Domains0Fast v from by decide) v
def root0Node54Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5)]
  | 3 => [(6,1)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,0)]
  | 9 => [(7,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(3,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(1,0)]
  | 50 => [(7,4)]
  | 51 => [(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(0,5),(1,3),(6,3)]
  | 55 => [(4,4),(7,2),(8,2)]
  | 56 => [(0,2)]
  | 57 => [(1,1)]
  | 58 => [(4,1),(8,1)]
  | 59 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node54Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,0)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(3,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(7,4)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,2)]
  | 57 => some [(1,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node54Domains1_fast_eq : root0Node54Domains1 = expandDomains root0Node54Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node54Domains1 v = expandDomains root0Node54Domains1Fast v from by decide) v
theorem root0Node54Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root0Node54Domains0 root0Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains0 root0Node54Domains1
    root0Node54Domains0Fast root0Node54Domains1Fast
    root0Node54Domains0_fast_eq root0Node54Domains1_fast_eq (by decide)
theorem root0Node54Step1_checked :
    checkReplacement table37 root0Node54Domains0 root0Node54Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node54Step1Chunk0_0_checked, root0Node54Step1Chunk0_1_checked, root0Node54Step1Chunk0_2_checked, root0Node54Step1Chunk0_3_checked, root0Node54Step1Chunk0_4_checked, root0Node54Step1Chunk0_5_checked, root0Node54Step1Chunk1_0_checked, root0Node54Step1Chunk1_1_checked, root0Node54Step1Chunk1_2_checked, root0Node54Step1Chunk1_3_checked, root0Node54Step1Chunk1_4_checked, root0Node54Step1Chunk1_5_checked, root0Node54Step1Chunk2_0_checked, root0Node54Step1Chunk2_1_checked, root0Node54Step1Chunk2_2_checked, root0Node54Step1Chunk2_3_checked, root0Node54Step1Chunk2_4_checked, root0Node54Step1Chunk2_5_checked, root0Node54Step1Chunk3_0_checked, root0Node54Step1Chunk3_1_checked, root0Node54Step1Chunk3_2_checked, root0Node54Step1Chunk3_3_checked, root0Node54Step1Chunk3_4_checked, root0Node54Step1Chunk3_5_checked, root0Node54Step1Chunk4_0_checked, root0Node54Step1Chunk4_1_checked, root0Node54Step1Chunk4_2_checked, root0Node54Step1Chunk4_3_checked, root0Node54Step1Chunk4_4_checked, root0Node54Step1Chunk4_5_checked, root0Node54Step1Chunk5_0_checked, root0Node54Step1Chunk5_1_checked, root0Node54Step1Chunk5_2_checked, root0Node54Step1Chunk5_3_checked, root0Node54Step1Chunk5_4_checked, root0Node54Step1Chunk5_5_checked, root0Node54Step1Chunk6_0_checked, root0Node54Step1Chunk6_1_checked, root0Node54Step1Chunk6_2_checked, root0Node54Step1Chunk6_3_checked, root0Node54Step1Chunk6_4_checked, root0Node54Step1Chunk6_5_checked, root0Node54Step1Chunk7_0_checked, root0Node54Step1Chunk7_1_checked, root0Node54Step1Chunk7_2_checked, root0Node54Step1Chunk7_3_checked, root0Node54Step1Chunk7_4_checked, root0Node54Step1Chunk7_5_checked, root0Node54Step1Chunk8_0_checked, root0Node54Step1Chunk8_1_checked, root0Node54Step1Chunk8_2_checked, root0Node54Step1Chunk8_3_checked, root0Node54Step1Chunk8_4_checked, root0Node54Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node54Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5)]
  | 3 => [(6,1)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,0)]
  | 9 => [(7,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(3,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(7,4)]
  | 51 => [(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(0,2)]
  | 57 => [(1,1)]
  | 58 => [(4,1),(8,1)]
  | 59 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root0Node54Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,0)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(3,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(7,4)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(0,2)]
  | 57 => some [(1,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node54Domains2_fast_eq : root0Node54Domains2 = expandDomains root0Node54Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node54Domains2 v = expandDomains root0Node54Domains2Fast v from by decide) v
theorem root0Node54Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root0Node54Domains1 root0Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node54Domains1 root0Node54Domains2
    root0Node54Domains1Fast root0Node54Domains2Fast
    root0Node54Domains1_fast_eq root0Node54Domains2_fast_eq (by decide)
theorem root0Node54Step2_checked :
    checkReplacement table40 root0Node54Domains1 root0Node54Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node54Step2Chunk0_0_checked, root0Node54Step2Chunk0_1_checked, root0Node54Step2Chunk0_2_checked, root0Node54Step2Chunk0_3_checked, root0Node54Step2Chunk0_4_checked, root0Node54Step2Chunk0_5_checked, root0Node54Step2Chunk1_0_checked, root0Node54Step2Chunk1_1_checked, root0Node54Step2Chunk1_2_checked, root0Node54Step2Chunk1_3_checked, root0Node54Step2Chunk1_4_checked, root0Node54Step2Chunk1_5_checked, root0Node54Step2Chunk2_0_checked, root0Node54Step2Chunk2_1_checked, root0Node54Step2Chunk2_2_checked, root0Node54Step2Chunk2_3_checked, root0Node54Step2Chunk2_4_checked, root0Node54Step2Chunk2_5_checked, root0Node54Step2Chunk3_0_checked, root0Node54Step2Chunk3_1_checked, root0Node54Step2Chunk3_2_checked, root0Node54Step2Chunk3_3_checked, root0Node54Step2Chunk3_4_checked, root0Node54Step2Chunk3_5_checked, root0Node54Step2Chunk4_0_checked, root0Node54Step2Chunk4_1_checked, root0Node54Step2Chunk4_2_checked, root0Node54Step2Chunk4_3_checked, root0Node54Step2Chunk4_4_checked, root0Node54Step2Chunk4_5_checked, root0Node54Step2Chunk5_0_checked, root0Node54Step2Chunk5_1_checked, root0Node54Step2Chunk5_2_checked, root0Node54Step2Chunk5_3_checked, root0Node54Step2Chunk5_4_checked, root0Node54Step2Chunk5_5_checked, root0Node54Step2Chunk6_0_checked, root0Node54Step2Chunk6_1_checked, root0Node54Step2Chunk6_2_checked, root0Node54Step2Chunk6_3_checked, root0Node54Step2Chunk6_4_checked, root0Node54Step2Chunk6_5_checked, root0Node54Step2Chunk7_0_checked, root0Node54Step2Chunk7_1_checked, root0Node54Step2Chunk7_2_checked, root0Node54Step2Chunk7_3_checked, root0Node54Step2Chunk7_4_checked, root0Node54Step2Chunk7_5_checked, root0Node54Step2Chunk8_0_checked, root0Node54Step2Chunk8_1_checked, root0Node54Step2Chunk8_2_checked, root0Node54Step2Chunk8_3_checked, root0Node54Step2Chunk8_4_checked, root0Node54Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
