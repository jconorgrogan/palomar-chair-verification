module

public import SpectreFinite.RadiusFourRoot6Part10
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable4
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node36Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(5,1)]
  | 9 => [(0,1)]
  | 10 => [(6,2)]
  | 11 => [(1,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0)]
  | 17 => [(2,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0)]
  | 25 => [(3,2)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(8,1)]
  | 44 => [(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5)]
  | 51 => [(7,0)]
  | 52 => [(4,3)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1)]
  | 56 => [(4,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(2,0)]
  | _ => [(7,3)]
def root6Node36Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(5,1)]
  | 9 => some [(0,1)]
  | 10 => some [(6,2)]
  | 11 => some [(1,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0)]
  | 17 => some [(2,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(3,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,0)]
  | _ => some [(7,3)]
theorem root6Node36Domains2_fast_eq : root6Node36Domains2 = expandDomains root6Node36Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node36Domains2 v = expandDomains root6Node36Domains2Fast v from by decide) v
theorem root6Node36Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root6Node36Domains1 root6Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node36Domains1 root6Node36Domains2
    root6Node36Domains1Fast root6Node36Domains2Fast
    root6Node36Domains1_fast_eq root6Node36Domains2_fast_eq (by decide)
theorem root6Node36Step2_checked :
    checkReplacement table39 root6Node36Domains1 root6Node36Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node36Step2Chunk0_0_checked, root6Node36Step2Chunk0_1_checked, root6Node36Step2Chunk0_2_checked, root6Node36Step2Chunk0_3_checked, root6Node36Step2Chunk0_4_checked, root6Node36Step2Chunk0_5_checked, root6Node36Step2Chunk1_0_checked, root6Node36Step2Chunk1_1_checked, root6Node36Step2Chunk1_2_checked, root6Node36Step2Chunk1_3_checked, root6Node36Step2Chunk1_4_checked, root6Node36Step2Chunk1_5_checked, root6Node36Step2Chunk2_0_checked, root6Node36Step2Chunk2_1_checked, root6Node36Step2Chunk2_2_checked, root6Node36Step2Chunk2_3_checked, root6Node36Step2Chunk2_4_checked, root6Node36Step2Chunk2_5_checked, root6Node36Step2Chunk3_0_checked, root6Node36Step2Chunk3_1_checked, root6Node36Step2Chunk3_2_checked, root6Node36Step2Chunk3_3_checked, root6Node36Step2Chunk3_4_checked, root6Node36Step2Chunk3_5_checked, root6Node36Step2Chunk4_0_checked, root6Node36Step2Chunk4_1_checked, root6Node36Step2Chunk4_2_checked, root6Node36Step2Chunk4_3_checked, root6Node36Step2Chunk4_4_checked, root6Node36Step2Chunk4_5_checked, root6Node36Step2Chunk5_0_checked, root6Node36Step2Chunk5_1_checked, root6Node36Step2Chunk5_2_checked, root6Node36Step2Chunk5_3_checked, root6Node36Step2Chunk5_4_checked, root6Node36Step2Chunk5_5_checked, root6Node36Step2Chunk6_0_checked, root6Node36Step2Chunk6_1_checked, root6Node36Step2Chunk6_2_checked, root6Node36Step2Chunk6_3_checked, root6Node36Step2Chunk6_4_checked, root6Node36Step2Chunk6_5_checked, root6Node36Step2Chunk7_0_checked, root6Node36Step2Chunk7_1_checked, root6Node36Step2Chunk7_2_checked, root6Node36Step2Chunk7_3_checked, root6Node36Step2Chunk7_4_checked, root6Node36Step2Chunk7_5_checked, root6Node36Step2Chunk8_0_checked, root6Node36Step2Chunk8_1_checked, root6Node36Step2Chunk8_2_checked, root6Node36Step2Chunk8_3_checked, root6Node36Step2Chunk8_4_checked, root6Node36Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node36Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node36Domains2 (.output 17) = true := by decide
def root6Node37Domains0 : Domains 61 State := restrict root6Node27Domains3 3 (7,4)
def root6Node37Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(5,1),(8,1)]
  | 9 => some [(0,1),(6,5)]
  | 10 => some [(0,4),(6,2)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,3)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(3,2),(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(3,1),(5,1),(7,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node37Domains0_fast_eq : root6Node37Domains0 = expandDomains root6Node37Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node37Domains0 v = expandDomains root6Node37Domains0Fast v from by decide) v
def root6Node37Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,3),(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0),(7,0)]
  | 17 => [(2,3),(2,5),(4,3)]
  | 18 => [(0,1),(6,5)]
  | 19 => [(0,4),(6,2)]
  | 20 => [(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(4,5),(8,5)]
  | 27 => [(1,0),(7,0)]
  | 28 => [(4,3),(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(3,1),(5,1),(7,1)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(7,4),(8,0)]
  | 37 => [(1,3),(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,3)]
  | 43 => [(5,1),(5,4),(8,1)]
  | 44 => [(0,1),(6,4),(6,5)]
  | 45 => [(0,4),(1,2),(6,2)]
  | 46 => [(5,4),(8,4)]
  | 47 => [(0,0),(6,4)]
  | 48 => [(1,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(5,5),(7,5),(8,5)]
  | 51 => [(0,3),(1,0),(7,0)]
  | 52 => [(4,3),(7,1),(8,1)]
  | 53 => [(1,5),(3,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(4,1),(8,1)]
  | 56 => [(4,2),(4,4),(7,2),(8,2)]
  | 57 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => [(1,3),(3,3),(5,3),(7,3),(8,3)]
def root6Node37Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0),(7,0)]
  | 17 => some [(2,3),(2,5),(4,3)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(3,1),(5,1),(7,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node37Domains1_fast_eq : root6Node37Domains1 = expandDomains root6Node37Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node37Domains1 v = expandDomains root6Node37Domains1Fast v from by decide) v
theorem root6Node37Step1Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root6Node37Domains0 root6Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node37Domains0 root6Node37Domains1
    root6Node37Domains0Fast root6Node37Domains1Fast
    root6Node37Domains0_fast_eq root6Node37Domains1_fast_eq (by decide)
theorem root6Node37Step1_checked :
    checkReplacement table4 root6Node37Domains0 root6Node37Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node37Step1Chunk0_0_checked, root6Node37Step1Chunk0_1_checked, root6Node37Step1Chunk0_2_checked, root6Node37Step1Chunk0_3_checked, root6Node37Step1Chunk0_4_checked, root6Node37Step1Chunk0_5_checked, root6Node37Step1Chunk1_0_checked, root6Node37Step1Chunk1_1_checked, root6Node37Step1Chunk1_2_checked, root6Node37Step1Chunk1_3_checked, root6Node37Step1Chunk1_4_checked, root6Node37Step1Chunk1_5_checked, root6Node37Step1Chunk2_0_checked, root6Node37Step1Chunk2_1_checked, root6Node37Step1Chunk2_2_checked, root6Node37Step1Chunk2_3_checked, root6Node37Step1Chunk2_4_checked, root6Node37Step1Chunk2_5_checked, root6Node37Step1Chunk3_0_checked, root6Node37Step1Chunk3_1_checked, root6Node37Step1Chunk3_2_checked, root6Node37Step1Chunk3_3_checked, root6Node37Step1Chunk3_4_checked, root6Node37Step1Chunk3_5_checked, root6Node37Step1Chunk4_0_checked, root6Node37Step1Chunk4_1_checked, root6Node37Step1Chunk4_2_checked, root6Node37Step1Chunk4_3_checked, root6Node37Step1Chunk4_4_checked, root6Node37Step1Chunk4_5_checked, root6Node37Step1Chunk5_0_checked, root6Node37Step1Chunk5_1_checked, root6Node37Step1Chunk5_2_checked, root6Node37Step1Chunk5_3_checked, root6Node37Step1Chunk5_4_checked, root6Node37Step1Chunk5_5_checked, root6Node37Step1Chunk6_0_checked, root6Node37Step1Chunk6_1_checked, root6Node37Step1Chunk6_2_checked, root6Node37Step1Chunk6_3_checked, root6Node37Step1Chunk6_4_checked, root6Node37Step1Chunk6_5_checked, root6Node37Step1Chunk7_0_checked, root6Node37Step1Chunk7_1_checked, root6Node37Step1Chunk7_2_checked, root6Node37Step1Chunk7_3_checked, root6Node37Step1Chunk7_4_checked, root6Node37Step1Chunk7_5_checked, root6Node37Step1Chunk8_0_checked, root6Node37Step1Chunk8_1_checked, root6Node37Step1Chunk8_2_checked, root6Node37Step1Chunk8_3_checked, root6Node37Step1Chunk8_4_checked, root6Node37Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node38Domains0 : Domains 61 State := restrict root6Node37Domains1 16 (3,0)
def root6Node38Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,3),(2,5),(4,3)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(3,1),(5,1),(7,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node38Domains0_fast_eq : root6Node38Domains0 = expandDomains root6Node38Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node38Domains0 v = expandDomains root6Node38Domains0Fast v from by decide) v
def root6Node38Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,3),(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(0,1),(6,5)]
  | 19 => [(0,4),(6,2)]
  | 20 => [(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(4,5),(8,5)]
  | 27 => [(1,0),(7,0)]
  | 28 => [(4,3),(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(7,4),(8,0)]
  | 37 => [(1,3),(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(5,1),(5,4),(8,1)]
  | 44 => [(0,1),(6,4),(6,5)]
  | 45 => [(0,4),(1,2),(6,2)]
  | 46 => [(5,4),(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5),(7,5),(8,5)]
  | 51 => [(0,3),(1,0),(7,0)]
  | 52 => [(4,3),(7,1),(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1),(8,1)]
  | 56 => [(4,2),(4,4),(7,2),(8,2)]
  | 57 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => [(0,5),(4,5),(5,5),(8,5)]
  | 59 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
def root6Node38Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1),(5,4),(8,1)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(4,5),(5,5),(8,5)]
  | 59 => some [(2,0),(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root6Node38Domains1_fast_eq : root6Node38Domains1 = expandDomains root6Node38Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node38Domains1 v = expandDomains root6Node38Domains1Fast v from by decide) v
theorem root6Node38Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root6Node38Domains0 root6Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains0 root6Node38Domains1
    root6Node38Domains0Fast root6Node38Domains1Fast
    root6Node38Domains0_fast_eq root6Node38Domains1_fast_eq (by decide)
theorem root6Node38Step1_checked :
    checkReplacement table40 root6Node38Domains0 root6Node38Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node38Step1Chunk0_0_checked, root6Node38Step1Chunk0_1_checked, root6Node38Step1Chunk0_2_checked, root6Node38Step1Chunk0_3_checked, root6Node38Step1Chunk0_4_checked, root6Node38Step1Chunk0_5_checked, root6Node38Step1Chunk1_0_checked, root6Node38Step1Chunk1_1_checked, root6Node38Step1Chunk1_2_checked, root6Node38Step1Chunk1_3_checked, root6Node38Step1Chunk1_4_checked, root6Node38Step1Chunk1_5_checked, root6Node38Step1Chunk2_0_checked, root6Node38Step1Chunk2_1_checked, root6Node38Step1Chunk2_2_checked, root6Node38Step1Chunk2_3_checked, root6Node38Step1Chunk2_4_checked, root6Node38Step1Chunk2_5_checked, root6Node38Step1Chunk3_0_checked, root6Node38Step1Chunk3_1_checked, root6Node38Step1Chunk3_2_checked, root6Node38Step1Chunk3_3_checked, root6Node38Step1Chunk3_4_checked, root6Node38Step1Chunk3_5_checked, root6Node38Step1Chunk4_0_checked, root6Node38Step1Chunk4_1_checked, root6Node38Step1Chunk4_2_checked, root6Node38Step1Chunk4_3_checked, root6Node38Step1Chunk4_4_checked, root6Node38Step1Chunk4_5_checked, root6Node38Step1Chunk5_0_checked, root6Node38Step1Chunk5_1_checked, root6Node38Step1Chunk5_2_checked, root6Node38Step1Chunk5_3_checked, root6Node38Step1Chunk5_4_checked, root6Node38Step1Chunk5_5_checked, root6Node38Step1Chunk6_0_checked, root6Node38Step1Chunk6_1_checked, root6Node38Step1Chunk6_2_checked, root6Node38Step1Chunk6_3_checked, root6Node38Step1Chunk6_4_checked, root6Node38Step1Chunk6_5_checked, root6Node38Step1Chunk7_0_checked, root6Node38Step1Chunk7_1_checked, root6Node38Step1Chunk7_2_checked, root6Node38Step1Chunk7_3_checked, root6Node38Step1Chunk7_4_checked, root6Node38Step1Chunk7_5_checked, root6Node38Step1Chunk8_0_checked, root6Node38Step1Chunk8_1_checked, root6Node38Step1Chunk8_2_checked, root6Node38Step1Chunk8_3_checked, root6Node38Step1Chunk8_4_checked, root6Node38Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node38Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,3),(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(0,1),(6,5)]
  | 19 => [(0,4),(6,2)]
  | 20 => [(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(4,5),(8,5)]
  | 27 => [(1,0),(7,0)]
  | 28 => [(4,3),(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(7,4),(8,0)]
  | 37 => [(1,3),(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(5,1),(5,4),(8,1)]
  | 44 => [(0,1),(6,4),(6,5)]
  | 45 => [(0,4),(1,2),(6,2)]
  | 46 => [(5,4),(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5),(7,5),(8,5)]
  | 51 => [(0,3),(1,0),(7,0)]
  | 52 => [(4,3),(7,1),(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1),(8,1)]
  | 56 => [(4,2),(4,4),(8,2)]
  | 57 => [(1,4),(5,0),(5,3)]
  | 58 => [(0,5),(4,5),(5,5),(8,5)]
  | 59 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
def root6Node38Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1),(5,4),(8,1)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,2),(4,4),(8,2)]
  | 57 => some [(1,4),(5,0),(5,3)]
  | 58 => some [(0,5),(4,5),(5,5),(8,5)]
  | 59 => some [(2,0),(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root6Node38Domains2_fast_eq : root6Node38Domains2 = expandDomains root6Node38Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node38Domains2 v = expandDomains root6Node38Domains2Fast v from by decide) v
theorem root6Node38Step2Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root6Node38Domains1 root6Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node38Domains1 root6Node38Domains2
    root6Node38Domains1Fast root6Node38Domains2Fast
    root6Node38Domains1_fast_eq root6Node38Domains2_fast_eq (by decide)
theorem root6Node38Step2_checked :
    checkReplacement table36 root6Node38Domains1 root6Node38Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node38Step2Chunk0_0_checked, root6Node38Step2Chunk0_1_checked, root6Node38Step2Chunk0_2_checked, root6Node38Step2Chunk0_3_checked, root6Node38Step2Chunk0_4_checked, root6Node38Step2Chunk0_5_checked, root6Node38Step2Chunk1_0_checked, root6Node38Step2Chunk1_1_checked, root6Node38Step2Chunk1_2_checked, root6Node38Step2Chunk1_3_checked, root6Node38Step2Chunk1_4_checked, root6Node38Step2Chunk1_5_checked, root6Node38Step2Chunk2_0_checked, root6Node38Step2Chunk2_1_checked, root6Node38Step2Chunk2_2_checked, root6Node38Step2Chunk2_3_checked, root6Node38Step2Chunk2_4_checked, root6Node38Step2Chunk2_5_checked, root6Node38Step2Chunk3_0_checked, root6Node38Step2Chunk3_1_checked, root6Node38Step2Chunk3_2_checked, root6Node38Step2Chunk3_3_checked, root6Node38Step2Chunk3_4_checked, root6Node38Step2Chunk3_5_checked, root6Node38Step2Chunk4_0_checked, root6Node38Step2Chunk4_1_checked, root6Node38Step2Chunk4_2_checked, root6Node38Step2Chunk4_3_checked, root6Node38Step2Chunk4_4_checked, root6Node38Step2Chunk4_5_checked, root6Node38Step2Chunk5_0_checked, root6Node38Step2Chunk5_1_checked, root6Node38Step2Chunk5_2_checked, root6Node38Step2Chunk5_3_checked, root6Node38Step2Chunk5_4_checked, root6Node38Step2Chunk5_5_checked, root6Node38Step2Chunk6_0_checked, root6Node38Step2Chunk6_1_checked, root6Node38Step2Chunk6_2_checked, root6Node38Step2Chunk6_3_checked, root6Node38Step2Chunk6_4_checked, root6Node38Step2Chunk6_5_checked, root6Node38Step2Chunk7_0_checked, root6Node38Step2Chunk7_1_checked, root6Node38Step2Chunk7_2_checked, root6Node38Step2Chunk7_3_checked, root6Node38Step2Chunk7_4_checked, root6Node38Step2Chunk7_5_checked, root6Node38Step2Chunk8_0_checked, root6Node38Step2Chunk8_1_checked, root6Node38Step2Chunk8_2_checked, root6Node38Step2Chunk8_3_checked, root6Node38Step2Chunk8_4_checked, root6Node38Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node39Domains0 : Domains 61 State := restrict root6Node38Domains2 18 (0,1)
def root6Node39Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(0,1)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1),(5,4),(8,1)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,2),(4,4),(8,2)]
  | 57 => some [(1,4),(5,0),(5,3)]
  | 58 => some [(0,5),(4,5),(5,5),(8,5)]
  | 59 => some [(2,0),(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root6Node39Domains0_fast_eq : root6Node39Domains0 = expandDomains root6Node39Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node39Domains0 v = expandDomains root6Node39Domains0Fast v from by decide) v
def root6Node39Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(4,5),(8,5)]
  | 27 => [(1,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(8,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(5,1),(5,4)]
  | 44 => [(0,1),(6,4)]
  | 45 => [(1,2),(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(7,5),(8,5)]
  | 51 => [(0,3),(1,0)]
  | 52 => [(7,1),(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1),(8,1)]
  | 56 => [(4,2),(8,2)]
  | 57 => [(5,0),(5,3)]
  | 58 => [(4,5),(5,5),(8,5)]
  | 59 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
def root6Node39Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1),(5,4)]
  | 44 => some [(0,1),(6,4)]
  | 45 => some [(1,2),(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5),(8,5)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,2),(8,2)]
  | 57 => some [(5,0),(5,3)]
  | 58 => some [(4,5),(5,5),(8,5)]
  | 59 => some [(2,0),(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root6Node39Domains1_fast_eq : root6Node39Domains1 = expandDomains root6Node39Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node39Domains1 v = expandDomains root6Node39Domains1Fast v from by decide) v
theorem root6Node39Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root6Node39Domains0 root6Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains0 root6Node39Domains1
    root6Node39Domains0Fast root6Node39Domains1Fast
    root6Node39Domains0_fast_eq root6Node39Domains1_fast_eq (by decide)
theorem root6Node39Step1_checked :
    checkReplacement table37 root6Node39Domains0 root6Node39Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node39Step1Chunk0_0_checked, root6Node39Step1Chunk0_1_checked, root6Node39Step1Chunk0_2_checked, root6Node39Step1Chunk0_3_checked, root6Node39Step1Chunk0_4_checked, root6Node39Step1Chunk0_5_checked, root6Node39Step1Chunk1_0_checked, root6Node39Step1Chunk1_1_checked, root6Node39Step1Chunk1_2_checked, root6Node39Step1Chunk1_3_checked, root6Node39Step1Chunk1_4_checked, root6Node39Step1Chunk1_5_checked, root6Node39Step1Chunk2_0_checked, root6Node39Step1Chunk2_1_checked, root6Node39Step1Chunk2_2_checked, root6Node39Step1Chunk2_3_checked, root6Node39Step1Chunk2_4_checked, root6Node39Step1Chunk2_5_checked, root6Node39Step1Chunk3_0_checked, root6Node39Step1Chunk3_1_checked, root6Node39Step1Chunk3_2_checked, root6Node39Step1Chunk3_3_checked, root6Node39Step1Chunk3_4_checked, root6Node39Step1Chunk3_5_checked, root6Node39Step1Chunk4_0_checked, root6Node39Step1Chunk4_1_checked, root6Node39Step1Chunk4_2_checked, root6Node39Step1Chunk4_3_checked, root6Node39Step1Chunk4_4_checked, root6Node39Step1Chunk4_5_checked, root6Node39Step1Chunk5_0_checked, root6Node39Step1Chunk5_1_checked, root6Node39Step1Chunk5_2_checked, root6Node39Step1Chunk5_3_checked, root6Node39Step1Chunk5_4_checked, root6Node39Step1Chunk5_5_checked, root6Node39Step1Chunk6_0_checked, root6Node39Step1Chunk6_1_checked, root6Node39Step1Chunk6_2_checked, root6Node39Step1Chunk6_3_checked, root6Node39Step1Chunk6_4_checked, root6Node39Step1Chunk6_5_checked, root6Node39Step1Chunk7_0_checked, root6Node39Step1Chunk7_1_checked, root6Node39Step1Chunk7_2_checked, root6Node39Step1Chunk7_3_checked, root6Node39Step1Chunk7_4_checked, root6Node39Step1Chunk7_5_checked, root6Node39Step1Chunk8_0_checked, root6Node39Step1Chunk8_1_checked, root6Node39Step1Chunk8_2_checked, root6Node39Step1Chunk8_3_checked, root6Node39Step1Chunk8_4_checked, root6Node39Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
