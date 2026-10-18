module

public import SpectreFinite.RadiusFourRoot0Part4
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable13
public import SpectreFinite.RadiusFourTable3
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node10Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(8,1)]
  | 5 => [(7,2)]
  | 6 => [(7,4)]
  | 7 => [(1,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(5,5)]
  | 11 => [(1,1)]
  | 12 => [(8,1)]
  | 13 => [(6,5)]
  | 14 => [(0,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(3,0)]
  | 22 => [(2,5)]
  | 23 => [(6,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(8,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(8,1)]
  | 59 => [(6,5)]
  | _ => [(0,4)]
def root0Node10Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(1,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(5,5)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(2,5)]
  | 23 => some [(6,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(8,1)]
  | 59 => some [(6,5)]
  | _ => some [(0,4)]
theorem root0Node10Domains2_fast_eq : root0Node10Domains2 = expandDomains root0Node10Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node10Domains2 v = expandDomains root0Node10Domains2Fast v from by decide) v
theorem root0Node10Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root0Node10Domains1 root0Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains1 root0Node10Domains2
    root0Node10Domains1Fast root0Node10Domains2Fast
    root0Node10Domains1_fast_eq root0Node10Domains2_fast_eq (by decide)
theorem root0Node10Step2_checked :
    checkReplacement table39 root0Node10Domains1 root0Node10Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node10Step2Chunk0_0_checked, root0Node10Step2Chunk0_1_checked, root0Node10Step2Chunk0_2_checked, root0Node10Step2Chunk0_3_checked, root0Node10Step2Chunk0_4_checked, root0Node10Step2Chunk0_5_checked, root0Node10Step2Chunk1_0_checked, root0Node10Step2Chunk1_1_checked, root0Node10Step2Chunk1_2_checked, root0Node10Step2Chunk1_3_checked, root0Node10Step2Chunk1_4_checked, root0Node10Step2Chunk1_5_checked, root0Node10Step2Chunk2_0_checked, root0Node10Step2Chunk2_1_checked, root0Node10Step2Chunk2_2_checked, root0Node10Step2Chunk2_3_checked, root0Node10Step2Chunk2_4_checked, root0Node10Step2Chunk2_5_checked, root0Node10Step2Chunk3_0_checked, root0Node10Step2Chunk3_1_checked, root0Node10Step2Chunk3_2_checked, root0Node10Step2Chunk3_3_checked, root0Node10Step2Chunk3_4_checked, root0Node10Step2Chunk3_5_checked, root0Node10Step2Chunk4_0_checked, root0Node10Step2Chunk4_1_checked, root0Node10Step2Chunk4_2_checked, root0Node10Step2Chunk4_3_checked, root0Node10Step2Chunk4_4_checked, root0Node10Step2Chunk4_5_checked, root0Node10Step2Chunk5_0_checked, root0Node10Step2Chunk5_1_checked, root0Node10Step2Chunk5_2_checked, root0Node10Step2Chunk5_3_checked, root0Node10Step2Chunk5_4_checked, root0Node10Step2Chunk5_5_checked, root0Node10Step2Chunk6_0_checked, root0Node10Step2Chunk6_1_checked, root0Node10Step2Chunk6_2_checked, root0Node10Step2Chunk6_3_checked, root0Node10Step2Chunk6_4_checked, root0Node10Step2Chunk6_5_checked, root0Node10Step2Chunk7_0_checked, root0Node10Step2Chunk7_1_checked, root0Node10Step2Chunk7_2_checked, root0Node10Step2Chunk7_3_checked, root0Node10Step2Chunk7_4_checked, root0Node10Step2Chunk7_5_checked, root0Node10Step2Chunk8_0_checked, root0Node10Step2Chunk8_1_checked, root0Node10Step2Chunk8_2_checked, root0Node10Step2Chunk8_3_checked, root0Node10Step2Chunk8_4_checked, root0Node10Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node10Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node10Domains2 (.output 4) = true := by decide
def root0Node11Domains0 : Domains 61 State := restrict root0Node7Domains4 11 (6,1)
def root0Node11Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(1,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(5,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(2,5)]
  | 23 => some [(6,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(4,4),(5,4),(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4),(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node11Domains0_fast_eq : root0Node11Domains0 = expandDomains root0Node11Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node11Domains0 v = expandDomains root0Node11Domains0Fast v from by decide) v
def root0Node11Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(8,1)]
  | 5 => [(7,2)]
  | 6 => [(7,4)]
  | 7 => [(1,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(5,5)]
  | 11 => [(6,1)]
  | 12 => [(8,1)]
  | 13 => [(6,5)]
  | 14 => [(0,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(3,0)]
  | 22 => [(2,5)]
  | 23 => [(6,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(8,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(8,1)]
  | 59 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root0Node11Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(1,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(5,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(2,5)]
  | 23 => some [(6,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node11Domains1_fast_eq : root0Node11Domains1 = expandDomains root0Node11Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node11Domains1 v = expandDomains root0Node11Domains1Fast v from by decide) v
theorem root0Node11Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root0Node11Domains0 root0Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains0 root0Node11Domains1
    root0Node11Domains0Fast root0Node11Domains1Fast
    root0Node11Domains0_fast_eq root0Node11Domains1_fast_eq (by decide)
theorem root0Node11Step1_checked :
    checkReplacement table37 root0Node11Domains0 root0Node11Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node11Step1Chunk0_0_checked, root0Node11Step1Chunk0_1_checked, root0Node11Step1Chunk0_2_checked, root0Node11Step1Chunk0_3_checked, root0Node11Step1Chunk0_4_checked, root0Node11Step1Chunk0_5_checked, root0Node11Step1Chunk1_0_checked, root0Node11Step1Chunk1_1_checked, root0Node11Step1Chunk1_2_checked, root0Node11Step1Chunk1_3_checked, root0Node11Step1Chunk1_4_checked, root0Node11Step1Chunk1_5_checked, root0Node11Step1Chunk2_0_checked, root0Node11Step1Chunk2_1_checked, root0Node11Step1Chunk2_2_checked, root0Node11Step1Chunk2_3_checked, root0Node11Step1Chunk2_4_checked, root0Node11Step1Chunk2_5_checked, root0Node11Step1Chunk3_0_checked, root0Node11Step1Chunk3_1_checked, root0Node11Step1Chunk3_2_checked, root0Node11Step1Chunk3_3_checked, root0Node11Step1Chunk3_4_checked, root0Node11Step1Chunk3_5_checked, root0Node11Step1Chunk4_0_checked, root0Node11Step1Chunk4_1_checked, root0Node11Step1Chunk4_2_checked, root0Node11Step1Chunk4_3_checked, root0Node11Step1Chunk4_4_checked, root0Node11Step1Chunk4_5_checked, root0Node11Step1Chunk5_0_checked, root0Node11Step1Chunk5_1_checked, root0Node11Step1Chunk5_2_checked, root0Node11Step1Chunk5_3_checked, root0Node11Step1Chunk5_4_checked, root0Node11Step1Chunk5_5_checked, root0Node11Step1Chunk6_0_checked, root0Node11Step1Chunk6_1_checked, root0Node11Step1Chunk6_2_checked, root0Node11Step1Chunk6_3_checked, root0Node11Step1Chunk6_4_checked, root0Node11Step1Chunk6_5_checked, root0Node11Step1Chunk7_0_checked, root0Node11Step1Chunk7_1_checked, root0Node11Step1Chunk7_2_checked, root0Node11Step1Chunk7_3_checked, root0Node11Step1Chunk7_4_checked, root0Node11Step1Chunk7_5_checked, root0Node11Step1Chunk8_0_checked, root0Node11Step1Chunk8_1_checked, root0Node11Step1Chunk8_2_checked, root0Node11Step1Chunk8_3_checked, root0Node11Step1Chunk8_4_checked, root0Node11Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node11Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(8,1)]
  | 5 => [(7,2)]
  | 6 => [(7,4)]
  | 7 => [(1,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(5,5)]
  | 11 => [(6,1)]
  | 12 => [(8,1)]
  | 13 => [(6,5)]
  | 14 => [(0,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(3,0)]
  | 22 => [(2,5)]
  | 23 => [(6,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(8,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(8,1)]
  | 59 => [(6,5)]
  | _ => [(0,4)]
def root0Node11Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(1,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(5,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(2,5)]
  | 23 => some [(6,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(8,1)]
  | 59 => some [(6,5)]
  | _ => some [(0,4)]
theorem root0Node11Domains2_fast_eq : root0Node11Domains2 = expandDomains root0Node11Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node11Domains2 v = expandDomains root0Node11Domains2Fast v from by decide) v
theorem root0Node11Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root0Node11Domains1 root0Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node11Domains1 root0Node11Domains2
    root0Node11Domains1Fast root0Node11Domains2Fast
    root0Node11Domains1_fast_eq root0Node11Domains2_fast_eq (by decide)
theorem root0Node11Step2_checked :
    checkReplacement table39 root0Node11Domains1 root0Node11Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node11Step2Chunk0_0_checked, root0Node11Step2Chunk0_1_checked, root0Node11Step2Chunk0_2_checked, root0Node11Step2Chunk0_3_checked, root0Node11Step2Chunk0_4_checked, root0Node11Step2Chunk0_5_checked, root0Node11Step2Chunk1_0_checked, root0Node11Step2Chunk1_1_checked, root0Node11Step2Chunk1_2_checked, root0Node11Step2Chunk1_3_checked, root0Node11Step2Chunk1_4_checked, root0Node11Step2Chunk1_5_checked, root0Node11Step2Chunk2_0_checked, root0Node11Step2Chunk2_1_checked, root0Node11Step2Chunk2_2_checked, root0Node11Step2Chunk2_3_checked, root0Node11Step2Chunk2_4_checked, root0Node11Step2Chunk2_5_checked, root0Node11Step2Chunk3_0_checked, root0Node11Step2Chunk3_1_checked, root0Node11Step2Chunk3_2_checked, root0Node11Step2Chunk3_3_checked, root0Node11Step2Chunk3_4_checked, root0Node11Step2Chunk3_5_checked, root0Node11Step2Chunk4_0_checked, root0Node11Step2Chunk4_1_checked, root0Node11Step2Chunk4_2_checked, root0Node11Step2Chunk4_3_checked, root0Node11Step2Chunk4_4_checked, root0Node11Step2Chunk4_5_checked, root0Node11Step2Chunk5_0_checked, root0Node11Step2Chunk5_1_checked, root0Node11Step2Chunk5_2_checked, root0Node11Step2Chunk5_3_checked, root0Node11Step2Chunk5_4_checked, root0Node11Step2Chunk5_5_checked, root0Node11Step2Chunk6_0_checked, root0Node11Step2Chunk6_1_checked, root0Node11Step2Chunk6_2_checked, root0Node11Step2Chunk6_3_checked, root0Node11Step2Chunk6_4_checked, root0Node11Step2Chunk6_5_checked, root0Node11Step2Chunk7_0_checked, root0Node11Step2Chunk7_1_checked, root0Node11Step2Chunk7_2_checked, root0Node11Step2Chunk7_3_checked, root0Node11Step2Chunk7_4_checked, root0Node11Step2Chunk7_5_checked, root0Node11Step2Chunk8_0_checked, root0Node11Step2Chunk8_1_checked, root0Node11Step2Chunk8_2_checked, root0Node11Step2Chunk8_3_checked, root0Node11Step2Chunk8_4_checked, root0Node11Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node11Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node11Domains2 (.output 5) = true := by decide
def root0Node12Domains0 : Domains 61 State := restrict root0Node6Domains2 21 (5,0)
def root0Node12Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 5 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => some [(0,1),(1,4),(7,4)]
  | 7 => some [(0,5),(1,3),(6,2),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(8,4)]
  | 9 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 10 => some [(3,2),(5,2),(5,5),(7,2)]
  | 11 => some [(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 12 => some [(4,1),(7,5),(8,1),(8,5)]
  | 13 => some [(0,2),(1,0),(6,0),(6,5)]
  | 14 => some [(0,4),(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,4),(1,5),(6,5)]
  | 16 => some [(0,4),(0,5),(6,1),(6,2)]
  | 17 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 18 => some [(4,0),(7,0),(7,4),(8,0)]
  | 19 => some [(1,3),(7,3),(8,3)]
  | 20 => some [(5,2),(5,5),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(2,5),(4,5)]
  | 23 => some [(1,0),(6,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 27 => some [(0,1),(1,4),(6,4),(6,5)]
  | 28 => some [(0,4),(0,5),(1,2),(6,2)]
  | 29 => some [(4,4),(5,4),(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(6,3),(7,3)]
  | 34 => some [(4,2),(7,2),(8,2)]
  | 35 => some [(5,5),(7,5),(8,5)]
  | 36 => some [(0,3),(1,0),(6,0),(7,0)]
  | 37 => some [(4,3),(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1),(5,1),(8,1)]
  | 41 => some [(0,1),(0,2),(6,5)]
  | 42 => some [(0,4),(1,1),(6,2)]
  | 43 => some [(4,2),(4,4),(8,2)]
  | 44 => some [(1,4),(5,0),(5,3)]
  | 45 => some [(0,5),(4,5),(5,5),(8,5)]
  | 46 => some [(2,0),(7,0)]
  | 47 => some [(7,3),(8,3)]
  | 48 => some [(5,2),(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0),(8,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4),(7,5),(8,4)]
  | 51 => some [(0,0),(0,5),(6,0),(6,3)]
  | 52 => some [(3,1),(4,4),(7,2)]
  | 53 => some [(0,1),(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,2),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2),(8,4)]
  | 56 => some [(0,2),(1,5),(6,0),(8,2)]
  | 57 => some [(1,1),(5,0),(6,1),(7,1)]
  | 58 => some [(4,1),(4,5),(7,5),(8,1)]
  | 59 => some [(0,2),(1,0),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node12Domains0_fast_eq : root0Node12Domains0 = expandDomains root0Node12Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node12Domains0 v = expandDomains root0Node12Domains0Fast v from by decide) v
def root0Node12Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0),(7,0),(8,0)]
  | 1 => [(4,3),(7,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 5 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => [(0,1),(1,4),(7,4)]
  | 7 => [(0,5),(6,2),(6,3)]
  | 8 => [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 9 => [(0,0),(1,3),(3,3),(7,3)]
  | 10 => [(3,2),(5,2),(5,5),(7,2)]
  | 11 => [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 12 => [(4,1),(7,5),(8,5)]
  | 13 => [(0,2),(1,0),(6,0)]
  | 14 => [(1,1),(3,1),(7,1)]
  | 15 => [(0,1),(1,5),(6,5)]
  | 16 => [(0,4),(6,1),(6,2)]
  | 17 => [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 18 => [(4,0),(7,4),(8,0)]
  | 19 => [(1,3),(7,3)]
  | 20 => [(5,2),(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0),(7,0)]
  | 24 => [(4,3),(7,1),(8,3)]
  | 25 => [(7,5),(8,5)]
  | 26 => [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 27 => [(0,1),(6,4),(6,5)]
  | 28 => [(0,4),(1,2),(6,2)]
  | 29 => [(5,4),(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0),(7,4)]
  | 33 => [(1,3),(6,3),(7,3)]
  | 34 => [(4,2),(7,2),(8,2)]
  | 35 => [(5,5),(7,5),(8,5)]
  | 36 => [(0,3),(1,0),(7,0)]
  | 37 => [(4,3),(7,1),(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(4,1),(5,1),(8,1)]
  | 41 => [(0,1),(0,2),(6,5)]
  | 42 => [(0,4),(1,1),(6,2)]
  | 43 => [(4,2),(4,4),(8,2)]
  | 44 => [(1,4),(5,0),(5,3)]
  | 45 => [(0,5),(4,5),(5,5),(8,5)]
  | 46 => [(2,0),(7,0)]
  | 47 => [(7,3),(8,3)]
  | 48 => [(5,2),(5,5),(8,5)]
  | 49 => [(1,0),(3,0),(7,0),(8,0)]
  | 50 => [(1,4),(3,4),(5,4),(7,4),(7,5),(8,4)]
  | 51 => [(0,0),(0,5),(6,0),(6,3)]
  | 52 => [(3,1),(4,4),(7,2)]
  | 53 => [(0,1),(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,2),(6,3)]
  | 55 => [(4,4),(7,2),(8,2),(8,4)]
  | 56 => [(0,2),(1,5),(6,0),(8,2)]
  | 57 => [(1,1),(5,0),(6,1),(7,1)]
  | 58 => [(4,1),(4,5),(7,5),(8,1)]
  | 59 => [(0,2),(1,0),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node12Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 5 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => some [(0,1),(1,4),(7,4)]
  | 7 => some [(0,5),(6,2),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(5,5),(7,2)]
  | 11 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 12 => some [(4,1),(7,5),(8,5)]
  | 13 => some [(0,2),(1,0),(6,0)]
  | 14 => some [(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,5),(6,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 18 => some [(4,0),(7,4),(8,0)]
  | 19 => some [(1,3),(7,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 27 => some [(0,1),(6,4),(6,5)]
  | 28 => some [(0,4),(1,2),(6,2)]
  | 29 => some [(5,4),(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(6,3),(7,3)]
  | 34 => some [(4,2),(7,2),(8,2)]
  | 35 => some [(5,5),(7,5),(8,5)]
  | 36 => some [(0,3),(1,0),(7,0)]
  | 37 => some [(4,3),(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1),(5,1),(8,1)]
  | 41 => some [(0,1),(0,2),(6,5)]
  | 42 => some [(0,4),(1,1),(6,2)]
  | 43 => some [(4,2),(4,4),(8,2)]
  | 44 => some [(1,4),(5,0),(5,3)]
  | 45 => some [(0,5),(4,5),(5,5),(8,5)]
  | 46 => some [(2,0),(7,0)]
  | 47 => some [(7,3),(8,3)]
  | 48 => some [(5,2),(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0),(8,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4),(7,5),(8,4)]
  | 51 => some [(0,0),(0,5),(6,0),(6,3)]
  | 52 => some [(3,1),(4,4),(7,2)]
  | 53 => some [(0,1),(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,2),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2),(8,4)]
  | 56 => some [(0,2),(1,5),(6,0),(8,2)]
  | 57 => some [(1,1),(5,0),(6,1),(7,1)]
  | 58 => some [(4,1),(4,5),(7,5),(8,1)]
  | 59 => some [(0,2),(1,0),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node12Domains1_fast_eq : root0Node12Domains1 = expandDomains root0Node12Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node12Domains1 v = expandDomains root0Node12Domains1Fast v from by decide) v
theorem root0Node12Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root0Node12Domains0 root0Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains0 root0Node12Domains1
    root0Node12Domains0Fast root0Node12Domains1Fast
    root0Node12Domains0_fast_eq root0Node12Domains1_fast_eq (by decide)
theorem root0Node12Step1_checked :
    checkReplacement table13 root0Node12Domains0 root0Node12Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node12Step1Chunk0_0_checked, root0Node12Step1Chunk0_1_checked, root0Node12Step1Chunk0_2_checked, root0Node12Step1Chunk0_3_checked, root0Node12Step1Chunk0_4_checked, root0Node12Step1Chunk0_5_checked, root0Node12Step1Chunk1_0_checked, root0Node12Step1Chunk1_1_checked, root0Node12Step1Chunk1_2_checked, root0Node12Step1Chunk1_3_checked, root0Node12Step1Chunk1_4_checked, root0Node12Step1Chunk1_5_checked, root0Node12Step1Chunk2_0_checked, root0Node12Step1Chunk2_1_checked, root0Node12Step1Chunk2_2_checked, root0Node12Step1Chunk2_3_checked, root0Node12Step1Chunk2_4_checked, root0Node12Step1Chunk2_5_checked, root0Node12Step1Chunk3_0_checked, root0Node12Step1Chunk3_1_checked, root0Node12Step1Chunk3_2_checked, root0Node12Step1Chunk3_3_checked, root0Node12Step1Chunk3_4_checked, root0Node12Step1Chunk3_5_checked, root0Node12Step1Chunk4_0_checked, root0Node12Step1Chunk4_1_checked, root0Node12Step1Chunk4_2_checked, root0Node12Step1Chunk4_3_checked, root0Node12Step1Chunk4_4_checked, root0Node12Step1Chunk4_5_checked, root0Node12Step1Chunk5_0_checked, root0Node12Step1Chunk5_1_checked, root0Node12Step1Chunk5_2_checked, root0Node12Step1Chunk5_3_checked, root0Node12Step1Chunk5_4_checked, root0Node12Step1Chunk5_5_checked, root0Node12Step1Chunk6_0_checked, root0Node12Step1Chunk6_1_checked, root0Node12Step1Chunk6_2_checked, root0Node12Step1Chunk6_3_checked, root0Node12Step1Chunk6_4_checked, root0Node12Step1Chunk6_5_checked, root0Node12Step1Chunk7_0_checked, root0Node12Step1Chunk7_1_checked, root0Node12Step1Chunk7_2_checked, root0Node12Step1Chunk7_3_checked, root0Node12Step1Chunk7_4_checked, root0Node12Step1Chunk7_5_checked, root0Node12Step1Chunk8_0_checked, root0Node12Step1Chunk8_1_checked, root0Node12Step1Chunk8_2_checked, root0Node12Step1Chunk8_3_checked, root0Node12Step1Chunk8_4_checked, root0Node12Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node12Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0),(7,0),(8,0)]
  | 1 => [(4,3),(7,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => [(2,1),(2,5),(4,1),(4,5)]
  | 5 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => [(0,1),(1,4),(7,4)]
  | 7 => [(0,5),(6,2),(6,3)]
  | 8 => [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 9 => [(0,0),(1,3),(3,3),(7,3)]
  | 10 => [(3,2),(5,2),(7,2)]
  | 11 => [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 12 => [(4,1),(7,5),(8,5)]
  | 13 => [(0,2),(1,0),(6,0)]
  | 14 => [(1,1),(3,1),(7,1)]
  | 15 => [(0,1),(1,5),(6,5)]
  | 16 => [(0,4),(6,1),(6,2)]
  | 17 => [(5,1),(5,4),(8,1),(8,4)]
  | 18 => [(4,0),(7,4),(8,0)]
  | 19 => [(1,3),(7,3)]
  | 20 => [(5,2),(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0),(7,0)]
  | 24 => [(4,3),(7,1),(8,3)]
  | 25 => [(7,5),(8,5)]
  | 26 => [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 27 => [(0,1),(6,4),(6,5)]
  | 28 => [(0,4),(1,2),(6,2)]
  | 29 => [(5,4),(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0),(7,4)]
  | 33 => [(1,3),(6,3),(7,3)]
  | 34 => [(4,2),(7,2),(8,2)]
  | 35 => [(5,5),(7,5),(8,5)]
  | 36 => [(0,3),(1,0),(7,0)]
  | 37 => [(4,3),(7,1),(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(4,1),(5,1),(8,1)]
  | 41 => [(0,1),(0,2),(6,5)]
  | 42 => [(0,4),(1,1),(6,2)]
  | 43 => [(4,2),(4,4),(8,2)]
  | 44 => [(1,4),(5,0),(5,3)]
  | 45 => [(0,5),(4,5),(5,5),(8,5)]
  | 46 => [(2,0),(7,0)]
  | 47 => [(7,3),(8,3)]
  | 48 => [(5,2),(5,5),(8,5)]
  | 49 => [(1,0),(3,0),(7,0),(8,0)]
  | 50 => [(1,4),(3,4),(5,4),(7,4),(7,5),(8,4)]
  | 51 => [(0,0),(0,5),(6,0),(6,3)]
  | 52 => [(3,1),(4,4),(7,2)]
  | 53 => [(0,1),(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,2),(6,3)]
  | 55 => [(4,4),(7,2),(8,2),(8,4)]
  | 56 => [(0,2),(1,5),(6,0),(8,2)]
  | 57 => [(1,1),(5,0),(6,1),(7,1)]
  | 58 => [(4,1),(4,5),(7,5),(8,1)]
  | 59 => [(0,2),(1,0),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node12Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1),(4,5)]
  | 5 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => some [(0,1),(1,4),(7,4)]
  | 7 => some [(0,5),(6,2),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 12 => some [(4,1),(7,5),(8,5)]
  | 13 => some [(0,2),(1,0),(6,0)]
  | 14 => some [(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,5),(6,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(5,1),(5,4),(8,1),(8,4)]
  | 18 => some [(4,0),(7,4),(8,0)]
  | 19 => some [(1,3),(7,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 27 => some [(0,1),(6,4),(6,5)]
  | 28 => some [(0,4),(1,2),(6,2)]
  | 29 => some [(5,4),(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(6,3),(7,3)]
  | 34 => some [(4,2),(7,2),(8,2)]
  | 35 => some [(5,5),(7,5),(8,5)]
  | 36 => some [(0,3),(1,0),(7,0)]
  | 37 => some [(4,3),(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1),(5,1),(8,1)]
  | 41 => some [(0,1),(0,2),(6,5)]
  | 42 => some [(0,4),(1,1),(6,2)]
  | 43 => some [(4,2),(4,4),(8,2)]
  | 44 => some [(1,4),(5,0),(5,3)]
  | 45 => some [(0,5),(4,5),(5,5),(8,5)]
  | 46 => some [(2,0),(7,0)]
  | 47 => some [(7,3),(8,3)]
  | 48 => some [(5,2),(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0),(8,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4),(7,5),(8,4)]
  | 51 => some [(0,0),(0,5),(6,0),(6,3)]
  | 52 => some [(3,1),(4,4),(7,2)]
  | 53 => some [(0,1),(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,2),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2),(8,4)]
  | 56 => some [(0,2),(1,5),(6,0),(8,2)]
  | 57 => some [(1,1),(5,0),(6,1),(7,1)]
  | 58 => some [(4,1),(4,5),(7,5),(8,1)]
  | 59 => some [(0,2),(1,0),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node12Domains2_fast_eq : root0Node12Domains2 = expandDomains root0Node12Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node12Domains2 v = expandDomains root0Node12Domains2Fast v from by decide) v
theorem root0Node12Step2Chunk0_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_0⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk0_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_1⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk0_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_2⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk0_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_3⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk0_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_4⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk0_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_5⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk1_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_0⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk1_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_1⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk1_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_2⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk1_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_3⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk1_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_4⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk1_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_5⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk2_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_0⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk2_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_1⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk2_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_2⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk2_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_3⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk2_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_4⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk2_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_5⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk3_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_0⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk3_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_1⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk3_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_2⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk3_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_3⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk3_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_4⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk3_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_5⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk4_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_0⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk4_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_1⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk4_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_2⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk4_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_3⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk4_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_4⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk4_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_5⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk5_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_0⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk5_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_1⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk5_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_2⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk5_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_3⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk5_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_4⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk5_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_5⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk6_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_0⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk6_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_1⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk6_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_2⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk6_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_3⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk6_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_4⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk6_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_5⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk7_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_0⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk7_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_1⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk7_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_2⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk7_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_3⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk7_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_4⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk7_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_5⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk8_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_0⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk8_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_1⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk8_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_2⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk8_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_3⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk8_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_4⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2Chunk8_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_5⟩
      root0Node12Domains1 root0Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains1 root0Node12Domains2
    root0Node12Domains1Fast root0Node12Domains2Fast
    root0Node12Domains1_fast_eq root0Node12Domains2_fast_eq (by decide)
theorem root0Node12Step2_checked :
    checkReplacement table3 root0Node12Domains1 root0Node12Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node12Step2Chunk0_0_checked, root0Node12Step2Chunk0_1_checked, root0Node12Step2Chunk0_2_checked, root0Node12Step2Chunk0_3_checked, root0Node12Step2Chunk0_4_checked, root0Node12Step2Chunk0_5_checked, root0Node12Step2Chunk1_0_checked, root0Node12Step2Chunk1_1_checked, root0Node12Step2Chunk1_2_checked, root0Node12Step2Chunk1_3_checked, root0Node12Step2Chunk1_4_checked, root0Node12Step2Chunk1_5_checked, root0Node12Step2Chunk2_0_checked, root0Node12Step2Chunk2_1_checked, root0Node12Step2Chunk2_2_checked, root0Node12Step2Chunk2_3_checked, root0Node12Step2Chunk2_4_checked, root0Node12Step2Chunk2_5_checked, root0Node12Step2Chunk3_0_checked, root0Node12Step2Chunk3_1_checked, root0Node12Step2Chunk3_2_checked, root0Node12Step2Chunk3_3_checked, root0Node12Step2Chunk3_4_checked, root0Node12Step2Chunk3_5_checked, root0Node12Step2Chunk4_0_checked, root0Node12Step2Chunk4_1_checked, root0Node12Step2Chunk4_2_checked, root0Node12Step2Chunk4_3_checked, root0Node12Step2Chunk4_4_checked, root0Node12Step2Chunk4_5_checked, root0Node12Step2Chunk5_0_checked, root0Node12Step2Chunk5_1_checked, root0Node12Step2Chunk5_2_checked, root0Node12Step2Chunk5_3_checked, root0Node12Step2Chunk5_4_checked, root0Node12Step2Chunk5_5_checked, root0Node12Step2Chunk6_0_checked, root0Node12Step2Chunk6_1_checked, root0Node12Step2Chunk6_2_checked, root0Node12Step2Chunk6_3_checked, root0Node12Step2Chunk6_4_checked, root0Node12Step2Chunk6_5_checked, root0Node12Step2Chunk7_0_checked, root0Node12Step2Chunk7_1_checked, root0Node12Step2Chunk7_2_checked, root0Node12Step2Chunk7_3_checked, root0Node12Step2Chunk7_4_checked, root0Node12Step2Chunk7_5_checked, root0Node12Step2Chunk8_0_checked, root0Node12Step2Chunk8_1_checked, root0Node12Step2Chunk8_2_checked, root0Node12Step2Chunk8_3_checked, root0Node12Step2Chunk8_4_checked, root0Node12Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
